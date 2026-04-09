import Lean
import Lean.Meta
import Lean.Elab.Command
import Lean.PrettyPrinter

open Lean Meta Elab Command

-- Структура леммы

structure LemmaInfo where
  name    : Name
  typeStr : String
  role    : String
  deriving Repr

-- Дерево доказательств для сборочной теоремы

inductive ProofTree where
  | leaf    : Name → ProofTree
  | conj    : ProofTree → ProofTree → ProofTree
  | disjL   : ProofTree → ProofTree
  | iff_    : Name → Name → ProofTree
  | impl    : Nat → ProofTree → ProofTree
  deriving Inhabited

partial def renderProof (t : ProofTree) : String :=
  match t with
  | .leaf n      => toString n
  | .conj l r    => s!"⟨{renderProof l}, {renderProof r}⟩"
  | .disjL l     => s!"Or.inl ({renderProof l})  -- или Or.inr (...)"
  | .iff_ mp mpr => s!"⟨{mp}, {mpr}⟩"
  | .impl n b =>
    let args := (List.range n).map fun i => s!"h{i+1}"
    s!"fun {" ".intercalate args} => {renderProof b}"


-- Вспомогательные

partial def peelImpl (e : Expr) : List Expr × Expr :=
  match e with
  | .forallE _ d b .default =>
    if b.hasLooseBVars then ([], e)
    else let (rest, body) := peelImpl b; (d :: rest, body)
  | _ => ([], e)

partial def decompose
    (e        : Expr)
    (baseName : Name)
    (ctx      : Array Expr)
    (counter  : IO.Ref Nat)
    : MetaM (List LemmaInfo × ProofTree) := do
  let e ← whnfR e
  match e with

  | .app (.app (.const ``And _) lhs) rhs => do
    let (ll, lp) ← decompose lhs baseName ctx counter
    let (rl, rp) ← decompose rhs baseName ctx counter
    return (ll ++ rl, .conj lp rp)

  | .app (.app (.const ``Prod _) lhs) rhs => do
    let (ll, lp) ← decompose lhs baseName ctx counter
    let (rl, rp) ← decompose rhs baseName ctx counter
    return (ll ++ rl, .conj lp rp)

  | .app (.app (.const ``Or _) lhs) rhs => do
    let (ll, lp) ← decompose lhs baseName ctx counter
    let (rl, _)  ← decompose rhs baseName ctx counter
    let ll' := ll.map fun li => { li with role := "disj_left  (выберите эту ветку)" }
    let rl' := rl.map fun li => { li with role := "disj_right (или эту)" }
    return (ll' ++ rl', .disjL lp)

  | .app (.app (.const ``Iff _) lhs) rhs => do
    let idx1 ← counter.get; counter.set (idx1 + 1)
    let idx2 ← counter.get; counter.set (idx2 + 1)
    let mpName  := baseName ++ Name.mkSimple s!"_lem_{idx1}"
    let mprName := baseName ++ Name.mkSimple s!"_lem_{idx2}"
    -- mp: ∀ ctx, lhs → rhs
    let mpStr ← withLocalDecl `h .default lhs fun fv => do
      toString <$> PrettyPrinter.ppExpr (← mkForallFVars (ctx.push fv) rhs)
    -- mpr: ∀ ctx, rhs → lhs
    let mprStr ← withLocalDecl `h .default rhs fun fv => do
      toString <$> PrettyPrinter.ppExpr (← mkForallFVars (ctx.push fv) lhs)
    return ([ { name := mpName,  typeStr := mpStr,  role := "iff_mp  (→)" }
             ,{ name := mprName, typeStr := mprStr, role := "iff_mpr (←)" } ],
            .iff_ mpName mprName)

  -- ∃
  | .app (.app (.const ``Exists _) _) _ => do
    let idx ← counter.get; counter.set (idx + 1)
    let n   := baseName ++ Name.mkSimple s!"_lem_{idx}"
    let str := toString (← PrettyPrinter.ppExpr (← mkForallFVars ctx e))
    return ([{ name := n, typeStr := str, role := "exists" }], .leaf n)

  | .forallE _ _ _ .default => do
    let (hyps, body) := peelImpl e
    if hyps.isEmpty then
      -- зависимый ∀ — атом
      let idx ← counter.get; counter.set (idx + 1)
      let n   := baseName ++ Name.mkSimple s!"_lem_{idx}"
      let str := toString (← PrettyPrinter.ppExpr (← mkForallFVars ctx e))
      return ([{ name := n, typeStr := str, role := "goal" }], .leaf n)
    else
      let rec addHyps : List Expr → Array Expr → MetaM (List LemmaInfo × ProofTree)
        | [],      acc => decompose body baseName acc counter
        | h :: hs, acc => withLocalDecl `h .default h fun fv =>
            addHyps hs (acc.push fv)
      let (ls, pt) ← addHyps hyps ctx
      return (ls, .impl hyps.length pt)

  | _ => do
    let idx ← counter.get; counter.set (idx + 1)
    let n   := baseName ++ Name.mkSimple s!"_lem_{idx}"
    let str := toString (← PrettyPrinter.ppExpr (← mkForallFVars ctx e))
    return ([{ name := n, typeStr := str, role := "goal" }], .leaf n)

partial def renderTree (e : Expr) (ctx : Array Expr) (pad : String := "") : MetaM String := do
  let e ← whnfR e
  match e with
  | .app (.app (.const ``And _) lhs) rhs =>
    return s!"{pad}∧\n{← renderTree lhs ctx (pad++"  ")}\n{← renderTree rhs ctx (pad++"  ")}"
  | .app (.app (.const ``Prod _) lhs) rhs =>
    return s!"{pad}∧\n{← renderTree lhs ctx (pad++"  ")}\n{← renderTree rhs ctx (pad++"  ")}"
  | .app (.app (.const ``Or _) lhs) rhs =>
    return s!"{pad}∨\n{← renderTree lhs ctx (pad++"  ")}\n{← renderTree rhs ctx (pad++"  ")}"
  | .app (.app (.const ``Iff _) lhs) rhs => do
    -- ppExpr на lhs/rhs напрямую — fvars из ctx уже в LocalContext
    let ls ← PrettyPrinter.ppExpr lhs
    let rs ← PrettyPrinter.ppExpr rhs
    return s!"{pad}↔\n{pad}  [mp]   {ls} → {rs}\n{pad}  [mpr]  {rs} → {ls}"
  | .app (.app (.const ``Exists _) _) _ => do
    return s!"{pad}[∃]  {← PrettyPrinter.ppExpr (← mkForallFVars ctx e)}"
  | .forallE _ _ _ .default => do
    let (hyps, body) := peelImpl e
    if hyps.isEmpty then
      return s!"{pad}[goal]  {← PrettyPrinter.ppExpr (← mkForallFVars ctx e)}"
    else
      let rec addHyps : List Expr → Array Expr → MetaM String
        | [],      acc => renderTree body acc pad
        | h :: hs, acc => withLocalDecl `h .default h fun fv => addHyps hs (acc.push fv)
      let hs ← hyps.mapM fun h => return toString (← PrettyPrinter.ppExpr h)
      let inner ← addHyps hyps ctx
      return s!"{pad}→ [{", ".intercalate hs}]\n{inner}"
  | _ =>
    return s!"{pad}[goal]  {← PrettyPrinter.ppExpr (← mkForallFVars ctx e)}"

def renderLemma (l : LemmaInfo) : String :=
  -- Пустое тело — пользователь заполняет сам
  s!"-- [{l.role}]\nlemma {l.name} : {l.typeStr} := by\n  _"

def runDecompose (theoremName : Name) : MetaM (List LemmaInfo × ProofTree × String) := do
  let env ← getEnv
  let info ← match env.find? theoremName with
    | some i => pure i
    | none   => throwError s!"Теорема «{theoremName}» не найдена"
  let origTypeStr := toString (← PrettyPrinter.ppExpr info.type)
  let counter ← IO.mkRef 1
  let (lemmas, proof) ← forallTelescope info.type fun fvars body =>
    decompose body theoremName fvars counter
  return (lemmas, proof, origTypeStr)

elab "#decompose_theorem" nameStx:ident : command => do
  let name := nameStx.getId
  let (lemmas, proof, origTypeStr) ← liftTermElabM <| runDecompose name
  if lemmas.isEmpty then logWarning "Нет лемм для вывода."
  else
    let finalThm :=
      "-- Основная теорема, собранная из лемм\n" ++
      s!"theorem {name}_assembled : {origTypeStr} := by\n  exact {renderProof proof}"

    let mut lines : Array String := #[
      s!"-- Decomposition of: {name}  ({lemmas.length} lemmas)"
    ]
    for l in lemmas do
      lines := lines.push (renderLemma l) |>.push ""
    lines := lines.push finalThm
    logInfo (String.intercalate "\n" lines.toList)

elab "#decompose_tree" nameStx:ident : command => do
  let name := nameStx.getId
  let env ← liftTermElabM getEnv
  let info ← liftTermElabM <| match env.find? name with
    | some i => pure i
    | none   => throwError s!"Теорема «{name}» не найдена"
  let treeStr ← liftTermElabM <|
    forallTelescope info.type fun fvars body => renderTree body fvars
  logInfo s!"Дерево «{name}»:\n{treeStr}"

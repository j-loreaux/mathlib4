/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Init
public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.DiscrTree.Util

/-!
# The `@[cfc_pull]` attribute

This file sets up the lemma database used by the `cfc_pull` tactic. It is deliberately
independent of `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.*`, so that lemmas
can eventually be tagged at their declaration sites.

A lemma tagged `@[cfc_pull]` must be an equation in which at least one side has `cfc` or `cfcₙ`
as its head symbol. Such a lemma is sorted into one of five *categories*, which record the
different ways the tactic can make use of it. Writing `F` for the function argument and `a` for
the element argument of a `cfc`/`cfcₙ` application:

| category  | shape                                              | example              |
| --------- | -------------------------------------------------- | -------------------- |
| `id`      | `cfc (fun x ↦ x) a = a`                             | `cfc_id'`            |
| `pull`    | `cfc F a = ⟨an expression in the algebra⟩`          | `cfc_mul`            |
| `scalar`  | `cfc (F : S → S) a = cfc (G : T → T) a`, `S ≠ T`    | `cfc_real_eq_complex`|
| `unital`  | `cfcₙ F a = cfc F a`                                | `cfcₙ_eq_cfc`        |
| `compose` | `cfc (F ∘ G) a = cfc F ⟨an expression in `a`⟩`      | `cfc_comp_pow`       |

See `Mathlib/Tactic/CFCPull/Spec.md` for the full specification.

## Implementation notes

Classification happens under `forallMetaTelescope` rather than `forallTelescope`: turning the
lemma's binders into metavariables means that type and instance arguments are indexed as
wildcards in the `DiscrTree`, and it makes the notion of "a variable of the lemma" (namely, an
unassigned metavariable) agree with what the tactic sees when it applies the lemma.
-/

public meta section

namespace Mathlib.Tactic.CFCPull

open Lean Meta

/-! ### Recognising applications of `cfc` and `cfcₙ` -/

/-- The name of the unital continuous functional calculus. Referred to by name rather than by
`` `` ``-quotation so that this file need not import the analysis library. -/
def cfcName : Name := `cfc

/-- The name of the non-unital continuous functional calculus. -/
def cfcₙName : Name := `cfcₙ

/-- The name of the class carrying the unital continuous functional calculus. -/
def cfcClassName : Name := `ContinuousFunctionalCalculus

/-- The name of the class carrying the non-unital continuous functional calculus. -/
def cfcₙClassName : Name := `NonUnitalContinuousFunctionalCalculus

/-- The pieces of an application `cfc f a` or `cfcₙ f a`.

Both constants take the scalar ring, the algebra and the predicate as their first three
arguments and the function and the element as their last two, which is all this structure
records; the instance arguments in between are irrelevant to us. -/
structure CFCApp where
  /-- `true` for `cfc`, `false` for `cfcₙ`. -/
  unital : Bool
  /-- The scalar ring `R`. -/
  R : Expr
  /-- The algebra `A`. -/
  A : Expr
  /-- The predicate `p : A → Prop` attached to the calculus. -/
  p : Expr
  /-- The function `f : R → R`. -/
  f : Expr
  /-- The element `a : A`. -/
  a : Expr
  deriving Inhabited

/-- Recognise an application of `cfc` or `cfcₙ`. -/
def CFCApp.match? (e : Expr) : Option CFCApp := do
  let .const n _ := e.getAppFn | none
  let unital ←
    if n == cfcName then pure true
    else if n == cfcₙName then pure false
    else none
  let args := e.getAppArgs
  -- `cfc` has 15 arguments and `cfcₙ` has 18; we only rely on the positions of the first three
  -- and the last two, so that the matcher survives a change to the instance arguments.
  guard <| args.size ≥ 5
  return { unital, R := args[0]!, A := args[1]!, p := args[2]!,
           f := args[args.size - 2]!, a := args[args.size - 1]! }

/-- Rebuild a `cfc`/`cfcₙ` application from a `CFCApp`, replacing the function argument.
The other arguments (including the instances) are reused verbatim. -/
def CFCApp.withFn (e : Expr) (f : Expr) : Expr :=
  let args := e.getAppArgs
  mkAppN e.getAppFn (args.set! (args.size - 2) f)

/-- Rebuild a `cfc`/`cfcₙ` application from a `CFCApp`, replacing the element argument. -/
def CFCApp.withElem (e : Expr) (a : Expr) : Expr :=
  let args := e.getAppArgs
  mkAppN e.getAppFn (args.set! (args.size - 1) a)

/-! ### Scalar rings -/

/-- The static approximation of the scalar ring of a tagged lemma.

`RingKey.any` covers both lemmas that are polymorphic over a `CommSemiring`/`CommRing` and
lemmas stated for `RCLike 𝕜`: there is no need to distinguish the two, because a lemma that
cannot be used at a given ring is rejected by instance synthesis when the tactic tries it. -/
inductive RingKey where
  /-- The lemma is about a fixed ring, with the given head constant (e.g. `Real`). -/
  | const (n : Name)
  /-- The lemma is polymorphic in its scalar ring. -/
  | any
  deriving Inhabited, BEq, Repr, DecidableEq

instance : ToMessageData RingKey where
  toMessageData
    | .const n => m!"{n}"
    | .any => m!"_"

/-- The `RingKey` of an expression denoting a scalar ring. -/
def RingKey.ofExpr (R : Expr) : RingKey :=
  match R.getAppFn with
  | .const n _ => .const n
  | _ => .any

/-- Whether a lemma with this ring key can be used at the ring `R` *without* a scalar
conversion. -/
def RingKey.matchesRing (k : RingKey) (R : Expr) : MetaM Bool := do
  match k with
  | .any => return true
  | .const n => return (← whnfR R).getAppFn.constName? == some n

/-! ### Lemma records -/

/-- A lemma of the form `cfc (fun x ↦ x) a = a`, used as the base case of the recursion. -/
structure IdLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- Whether the lemma is used right-to-left. -/
  symm : Bool
  /-- The scalar ring of the `cfc` application. -/
  ring : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the `cfc` side is the left-hand side (after `symm` has been taken into account). -/
  cfcOnLhs : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma with `cfc`/`cfcₙ` on one side and an algebraic expression on the other, e.g.
`cfc_mul : cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a`.

The subterms of the algebraic side which are themselves `cfc`/`cfcₙ` applications at the same
ring, unitality and element (here `cfc f a` and `cfc g a`) are called *holes*: they are the
positions at which the tactic recurses. -/
structure PullLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- Whether the lemma is used right-to-left. -/
  symm : Bool
  /-- The attribute priority. -/
  prio : Nat
  /-- The scalar ring of the `cfc` application. -/
  ring : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the `cfc` side is the left-hand side (after `symm` has been taken into account). -/
  cfcOnLhs : Bool
  /-- The number of holes on the algebraic side. -/
  numHoles : Nat
  deriving Inhabited, BEq, Repr

/-- A lemma relating the calculus over two different scalar rings, e.g.
`cfc_real_eq_complex : cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a`.

Such a lemma is an edge `src → tgt` of the scalar conversion graph; it is only ever used in the
direction in which it is stated (the reverse directions carry non-syntactic hypotheses). -/
structure ScalarLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- Whether the lemma is used right-to-left. -/
  symm : Bool
  /-- The ring converted *from*. -/
  src : RingKey
  /-- The ring converted *to*. -/
  tgt : RingKey
  /-- Whether the lemma is about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma relating the unital and non-unital calculi, i.e. `cfcₙ_eq_cfc`. It is usable in both
directions. -/
structure UnitalLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- Whether the lemma is used right-to-left. -/
  symm : Bool
  /-- The scalar ring of the two `cfc` applications. -/
  ring : RingKey
  /-- Whether the non-unital side is the left-hand side. -/
  nonUnitalOnLhs : Bool
  deriving Inhabited, BEq, Repr

/-- A lemma expressing a composition, e.g. `cfc_comp_pow : cfc (f <| · ^ n) a = cfc f (a ^ n)`.

One side (here the right) has a *structured* element; the other side's element is a bare
variable. `innerHead` is the head symbol of the structured element, which is what the lemma is
indexed by; for `cfc_comp'` it is `cfc` itself. -/
structure ComposeLemma where
  /-- The name of the tagged declaration. -/
  declName : Name
  /-- Whether the lemma is used right-to-left. -/
  symm : Bool
  /-- The attribute priority. -/
  prio : Nat
  /-- The scalar ring of the two `cfc` applications. -/
  ring : RingKey
  /-- Whether the lemmas are about `cfc` (`true`) or `cfcₙ` (`false`). -/
  unital : Bool
  /-- Whether the side with the structured element is the left-hand side. -/
  srcOnLhs : Bool
  /-- The head symbol of the structured element. -/
  innerHead : Name
  deriving Inhabited, BEq, Repr

/-- An entry added to the `cfc_pull` database. -/
inductive Entry where
  /-- An identity lemma. -/
  | id (l : IdLemma)
  /-- A pull lemma, together with its `DiscrTree` keys. -/
  | pull (l : PullLemma) (keys : Array DiscrTree.Key)
  /-- A scalar conversion lemma. -/
  | scalar (l : ScalarLemma)
  /-- A unitality conversion lemma. -/
  | unital (l : UnitalLemma)
  /-- A composition lemma. -/
  | compose (l : ComposeLemma)
  deriving Inhabited

/-- The `cfc_pull` lemma database. -/
structure Lemmas where
  /-- Pull lemmas, indexed by the head of their algebraic side (with holes as wildcards). -/
  pull : DiscrTree PullLemma := {}
  /-- Identity lemmas. -/
  id : Array IdLemma := #[]
  /-- Scalar conversion lemmas, viewed as the edges of a graph on ring keys. -/
  scalar : Array ScalarLemma := #[]
  /-- Unitality conversion lemmas. -/
  unital : Array UnitalLemma := #[]
  /-- Composition lemmas. -/
  compose : Array ComposeLemma := #[]
  deriving Inhabited

/-- Add an entry to the database. -/
def Lemmas.addEntry (s : Lemmas) : Entry → Lemmas
  | .id l => { s with id := s.id.push l }
  | .pull l keys => { s with pull := s.pull.insertKeyValue keys l }
  | .scalar l => { s with scalar := s.scalar.push l }
  | .unital l => { s with unital := s.unital.push l }
  | .compose l => { s with compose := s.compose.push l }

/-- The environment extension holding the `@[cfc_pull]` lemmas. -/
initialize cfcPullExt : SimpleScopedEnvExtension Entry Lemmas ←
  registerSimpleScopedEnvExtension {
    initial := {}
    addEntry := Lemmas.addEntry
  }

/-- The `@[cfc_pull]` lemmas available in the current environment. -/
def getLemmas : CoreM Lemmas := return cfcPullExt.getState (← getEnv)

/-! ### Finding and abstracting holes -/

/-- Replace every maximal subterm of `e` satisfying `isHole` by a fresh placeholder produced by
`mk`. Returns the resulting pattern together with the replaced subterms and the placeholders
used, both in left-to-right traversal order.

Subterms containing loose bound variables are never treated as holes; a hole underneath a binder
is fine as long as it does not mention the bound variable. -/
partial def abstractHoles (isHole : Expr → MetaM Bool) (mk : MetaM Expr) (e : Expr) :
    MetaM (Expr × Array Expr × Array Expr) := do
  let (pat, (holes, phs)) ← (go e).run (#[], #[])
  return (pat, holes, phs)
where
  /-- The traversal. -/
  go (e : Expr) : StateT (Array Expr × Array Expr) MetaM Expr := do
    if !e.hasLooseBVars then
      if ← isHole e then
        let ph ← mk
        modify fun (hs, ps) => (hs.push e, ps.push ph)
        return ph
    match e with
    | .app f x => return .app (← go f) (← go x)
    | .lam n t b bi => return .lam n (← go t) (← go b) bi
    | .forallE n t b bi => return .forallE n (← go t) (← go b) bi
    | .letE n t v b nd => return .letE n (← go t) (← go v) (← go b) nd
    | .mdata d b => return .mdata d (← go b)
    | .proj s i b => return .proj s i (← go b)
    | _ => return e

/-- Test whether `s` is a hole relative to the `cfc` application `ref`: an application of the
same calculus, at the same ring and element, whose function argument is a variable in the sense
of `isVar`. -/
def isHoleFor (ref : CFCApp) (isVar : Expr → MetaM Bool) (s : Expr) : MetaM Bool := do
  let some c := CFCApp.match? s | return false
  unless c.unital == ref.unital do return false
  unless ← isVar c.f do return false
  withNewMCtxDepth do
    unless ← isDefEq c.R ref.R do return false
    unless ← isDefEq c.a ref.a do return false
    return true

/-! ### Classification -/

/-- Instantiate a tagged lemma: returns its metavariables, their binder infos, the two sides of
the equation (swapped if the lemma is used right-to-left) and a proof of `lhs = rhs`. -/
def instantiateLemma (declName : Name) (symm : Bool) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr × Expr) := do
  let info ← getConstInfo declName
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let proof := .const declName lvls
  let (mvars, bis, type) ← forallMetaTelescope (info.type.instantiateLevelParams
    info.levelParams lvls)
  let some (_, lhs, rhs) := type.eq? |
    throwError "`{declName}` is not an equation"
  let proof := mkAppN proof mvars
  if symm then
    return (mvars, bis, rhs, lhs, ← mkEqSymm proof)
  else
    return (mvars, bis, lhs, rhs, proof)

/-- Build the database entry for `declName`, or throw an informative error explaining why the
lemma cannot be used by `cfc_pull`. -/
def mkEntry (declName : Name) (symm : Bool) (prio : Nat) : MetaM Entry := do
  let (_, _, lhs, rhs, _) ← instantiateLemma declName symm
  match CFCApp.match? lhs, CFCApp.match? rhs with
  | none, none =>
    throwError "@[cfc_pull] failed: neither side of `{declName}` has `cfc` or `cfcₙ` as its \
      head symbol.\n  {lhs} = {rhs}"
  | some c, none => mkPullEntry c rhs (cfcOnLhs := true)
  | none, some c => mkPullEntry c lhs (cfcOnLhs := false)
  | some cl, some cr => do
    let sameRing ← withNewMCtxDepth <| isDefEq cl.R cr.R
    if !sameRing then
      unless cl.unital == cr.unital do
        throwError "@[cfc_pull] failed: `{declName}` changes both the scalar ring and the \
          unitality of the functional calculus; such lemmas are not supported."
      return .scalar
        { declName, symm, src := .ofExpr cl.R, tgt := .ofExpr cr.R, unital := cl.unital }
    if cl.unital != cr.unital then
      return .unital { declName, symm, ring := .ofExpr cl.R, nonUnitalOnLhs := !cl.unital }
    -- same ring, same unitality: this must be a composition lemma
    if ← withNewMCtxDepth <| isDefEq cl.a cr.a then
      throwError "@[cfc_pull] failed: both sides of `{declName}` are applications of the same \
        functional calculus to the same element; there is nothing for `cfc_pull` to do."
    let srcOnLhs ←
      if cr.a.isMVar then pure true
      else if cl.a.isMVar then pure false
      else throwError "@[cfc_pull] failed: `{declName}` looks like a composition lemma, but \
        neither side applies the functional calculus to a bare variable."
    let src := if srcOnLhs then cl else cr
    let some innerHead := src.a.getAppFn.constName? |
      throwError "@[cfc_pull] failed: the element `{src.a}` in `{declName}` has no head constant \
        to index on."
    return .compose
      { declName, symm, prio, ring := .ofExpr cl.R, unital := cl.unital, srcOnLhs, innerHead }
where
  /-- Classify a lemma with a `cfc` application on exactly one side. -/
  mkPullEntry (c : CFCApp) (alg : Expr) (cfcOnLhs : Bool) : MetaM Entry := do
    if ← withNewMCtxDepth <| isDefEq alg c.a then
      return .id { declName, symm, ring := .ofExpr c.R, unital := c.unital, cfcOnLhs }
    let isVar (e : Expr) : MetaM Bool := return e.isMVar
    let (pat, holes, _) ← abstractHoles (isHoleFor c isVar) (mkFreshExprMVar c.A) alg
    for h in holes do
      if h.hasLooseBVars then
        throwError "@[cfc_pull] failed: in `{declName}`, the subterm `{h}` mentions a bound \
          variable, so `cfc_pull` cannot recurse into it."
    let keys ← DiscrTree.mkPath pat
    if keys.size ≤ 1 then
      throwError "@[cfc_pull] failed: the non-`cfc` side of `{declName}` is `{alg}`, which has \
        no head symbol to index on."
    return .pull
      { declName, symm, prio, ring := .ofExpr c.R, unital := c.unital, cfcOnLhs,
        numHoles := holes.size }
      keys

/-- The `cfc_pull` attribute marks lemmas for use by the `cfc_pull` tactic.

A tagged lemma must be an equation with `cfc` or `cfcₙ` as the head symbol of at least one side.
Use `@[cfc_pull ←]` to have the lemma used from right to left.

Examples of lemmas in each of the five categories the attribute recognises:
```
@[cfc_pull] cfc_id'            : cfc (fun x : R ↦ x) a = a
@[cfc_pull] cfc_mul            : cfc (fun x ↦ f x * g x) a = cfc f a * cfc g a
@[cfc_pull] cfc_real_eq_complex: cfc f a = cfc (fun x ↦ f x.re : ℂ → ℂ) a
@[cfc_pull] cfcₙ_eq_cfc        : cfcₙ f a = cfc f a
@[cfc_pull] cfc_comp_pow       : cfc (f <| · ^ n) a = cfc f (a ^ n)
```
-/
syntax (name := cfcPullAttr) "cfc_pull" (" ←" <|> " <-")? (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `cfcPullAttr
  descr := "lemma used by the `cfc_pull` tactic"
  add := fun declName stx kind => MetaM.run' do
    let symm := !stx[1].isNone
    let prio ← liftM <| getAttrParamOptPrio stx[2]
    cfcPullExt.add (← mkEntry declName symm prio) kind
}

/-- `#cfc_pull_lemmas` displays the contents of the `@[cfc_pull]` database. Useful for
debugging the tactic and its lemma set. -/
elab "#cfc_pull_lemmas" : command => Elab.Command.liftTermElabM do
  let l ← getLemmas
  let nm (n : Name) (symm : Bool) : MessageData := if symm then m!"{n} ←" else m!"{n}"
  let sec (header : String) (xs : Array MessageData) : MessageData :=
    m!"{header}:" ++ MessageData.nestD (MessageData.joinSep xs.toList m!"\n")
  logInfo <| MessageData.joinSep [
    sec "identity lemmas" <| l.id.map fun e =>
      m!"{nm e.declName e.symm} : ring := {e.ring}, unital := {e.unital}",
    sec "pull lemmas" <| l.pull.values.map fun e =>
      m!"{nm e.declName e.symm} : ring := {e.ring}, unital := {e.unital}, \
        holes := {e.numHoles}, prio := {e.prio}",
    sec "scalar lemmas" <| l.scalar.map fun e =>
      m!"{nm e.declName e.symm} : {e.src} → {e.tgt}, unital := {e.unital}",
    sec "unital lemmas" <| l.unital.map fun e =>
      m!"{nm e.declName e.symm} : ring := {e.ring}",
    sec "compose lemmas" <| l.compose.map fun e =>
      m!"{nm e.declName e.symm} : ring := {e.ring}, unital := {e.unital}, \
        inner := {e.innerHead}"] m!"\n"

/-- Tracing for the `cfc_pull` tactic. -/
initialize registerTraceClass `Tactic.cfc_pull

end Mathlib.Tactic.CFCPull

module

public import Aesop.BuiltinRules
public meta import Aesop.BuiltinRules
public meta import Lean.Elab.Tactic.RCases
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Finset.Attr
public import Mathlib.Data.Nat.Notation
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Continuity
public meta import Mathlib.Tactic.ToAdditive
public meta import Mathlib.Tactic.ToDual
public import Qq.Macro
public meta import Qq.MetaM

/-! # `congr_apply` tactic

Eliminates repeated nested quantifiers from a hypothesis and the goal in lockstep so that the
user only has to discharge the inner implication.
-/

@[expose] public section

open Lean Meta Elab Tactic Qq

theorem And.imp_right' {a b c : Prop} (h : a → b → c) : a ∧ b → a ∧ c := by grind

/--
Given a term with nested quantifiers (such as `h : ∀ x, ∃ y, P x y`),
and a goal with the same nested quantifiers (such as `⊢ ∀ x, ∃ y, Q x y`),
`congr_apply h` will simultaneously eliminate repeated quantifiers from `h` and `⊢` to
reduce the goal to `∀ x y, P x y → Q x y`.

Usage:
- `congr_apply h`: the basic usage.
- `congr_apply h : 3`: specify the depth to be 3, so that it does not decompose further.
- `congr_apply h with x y h : 2`: specify the depth, and then do `rintro` for the variables.
-/
syntax "congr_apply" term (" with " rintroPat+)? (" : " num)? : tactic

/-- Given a term `src` with nested quantifiers (such as `∀ x, ∃ y, P x y`),
and a goal `tgt` with the same nested quantifiers (such as `∀ x, ∃ y, Q x y`),
`mkCongrApply` will simultaneously eliminate repeated quantifiers from `src` and `tgt` to
extract the core implication (`new := ∀ x y, P x y → Q x y`) and then also return a proof that
`new` and `src` together imply `tgt`.
-/
meta partial def mkCongrApply (src tgt : Q(Prop)) (depth : Option ℕ) :
    MetaM ((new : Q(Prop)) × Q($new → $src → $tgt)) := do
  have dflt : (new : Q(Prop)) × Q($new → $src → $tgt) := ⟨q($src → $tgt), q(id)⟩
  if depth == some 0 then return dflt
  else if src.isForall then
    if !tgt.isForall then
      if depth.isSome then throwError "congr_apply: type mismatch" else return dflt
    forallBoundedTelescope src (some 1) fun ns p₁ ↦
    forallBoundedTelescope tgt (some 1) fun ns' p₂ ↦ do
    let t ← inferType ns[0]!
    if !(← isDefEq t (← inferType ns'[0]!)) then
      if depth.isSome then throwError "congr_apply: type mismatch" else return dflt
    have u := (← inferType t).sortLevel!
    have p₂ := p₂.applyFVarSubst ⟨[(ns'[0]!.fvarId!, ns[0]!)].toAssocList'⟩
    let ⟨new', h'⟩ ← mkCongrApply p₁ p₂ <| depth.map (· - 1)
    let new ← mkForallFVars ns new'
    return ⟨new,
      mkApp5 (mkConst ``Function.comp [0, 0, 0])
        new (← mkForallFVars ns (← mkArrow p₁ p₂)) (← mkArrow src tgt)
          (mkApp3 (mkConst ``forall_imp [u]) t (← mkLambdaFVars ns p₁) (← mkLambdaFVars ns p₂))
          (mkApp4 (mkConst ``forall_imp [u]) t (← mkLambdaFVars ns new')
            (← mkLambdaFVars ns (← mkArrow p₁ p₂)) (← mkLambdaFVars ns h'))⟩
  else match src, tgt with
  | ~q($t₁ ∧ $p₁), ~q($t₂ ∧ $p₂) =>
    if let .defEq _ ← isDefEqQ (u := 0) t₁ t₂ then
      let ⟨new', h'⟩ ← mkCongrApply p₁ p₂ <| depth.map (· - 1)
      return ⟨q($t₁ → $new'), q(fun h ↦ And.imp_right' <| $h' ∘ h)⟩
    else if depth.isSome then throwError "congr_apply: type mismatch" else return dflt
  -- TODO: or
  -- TODO: iff
  | ~q(@Exists $t₁ $e₁), ~q(@Exists $t₂ $e₂) =>
    lambdaBoundedTelescope e₁ 1 fun ns p₁ ↦
    lambdaBoundedTelescope e₂ 1 fun ns' p₂ ↦ do
    let t ← inferType ns[0]!
    assert! ← isDefEq t (← inferType ns'[0]!)
    have u := (← inferType t).sortLevel!
    have p₂ := p₂.applyFVarSubst ⟨[(ns'[0]!.fvarId!, ns[0]!)].toAssocList'⟩
    let ⟨new', h'⟩ ← mkCongrApply p₁ p₂ <| depth.map (· - 1)
    let new ← mkForallFVars ns new'
    return ⟨new,
      mkApp5 (mkConst ``Function.comp [0, 0, 0])
        new (← mkForallFVars ns (← mkArrow p₁ p₂)) (← mkArrow src tgt)
          (mkApp3 (mkConst ``Exists.imp [u]) t e₁ e₂)
          (mkApp4 (mkConst ``forall_imp [u]) t (← mkLambdaFVars ns new')
            (← mkLambdaFVars ns (← mkArrow p₁ p₂)) (← mkLambdaFVars ns h'))⟩
  | _, _ => if depth.isSome then throwError "congr_apply: type mismatch" else return dflt

/--
Given a term with nested quantifiers (such as `h : ∀ x, ∃ y, P x y`),
and a goal with the same nested quantifiers (such as `⊢ ∀ x, ∃ y, Q x y`),
`congr_apply h` will simultaneously eliminate repeated quantifiers from `h` and `⊢` to
reduce the goal to `∀ x y, P x y → Q x y`.

Usage:
- `congr_apply h`: the basic usage.
- `congr_apply h : 3`: specify the depth to be 3, so that it does not decompose further.
- `congr_apply h with x y h : 2`: specify the depth, and then do `rintro` for the variables.
-/
meta def congrApply (srcPf : Term) (depth := 0) (pats : Array (TSyntax `rintroPat) := #[]) :
    TacticM Unit :=
  withMainContext do
  let ⟨0, src, srcPf⟩ ← inferTypeQ (← elabTerm srcPf none)
    | throwError "congr_apply: source is not a proof"
  let ⟨1, ~q(Prop), tgt⟩ ← inferTypeQ (← getMainTarget)
    | throwError "congr_apply: target is not a proposition"
  let ⟨new, h⟩ ← mkCongrApply src tgt (if depth == 0 then none else some depth)
  let newGoal : Q($new) ← mkFreshExprMVar new
  (← getMainGoal).assign q($h $newGoal $srcPf)
  setGoals <| ← RCases.rintro pats none newGoal.mvarId!

elab_rules : tactic
  | `(tactic| congr_apply $src:term) => congrApply src
  | `(tactic| congr_apply $src:term : $depth:num) => congrApply src depth.getNat
  | `(tactic| congr_apply $src:term with $pats:rintroPat*) =>
    congrApply src 0 pats
  | `(tactic| congr_apply $src:term with $pats:rintroPat* : $depth:num) =>
    congrApply src depth.getNat pats

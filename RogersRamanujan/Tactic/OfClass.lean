module

public meta import Init.Grind.Cases
public meta import Init.Grind.Ext
public meta import Lean.Elab.Term.TermElabM
import Lean.Exception

/-! # ofClass% macro

There was a discussion in mathlib to change `AddMonoidHomClass.toAddMonoidHom` etc. to `.ofClass`,
but that has yet to be implemented (as of July 2026), so I'm implementing it here via a macro.
-/

namespace Mathlib.Tactic.OfClass

open Lean Elab Term

meta def builders : Std.HashMap Name Name := {
  (`AddActionHom, `AddActionSemiHomClass.toAddActionHom),
  (`AddEquiv, `AddEquivClass.toAddEquiv),
  (`AddHom, `AddHomClass.toAddHom),
  (`AddMonoidHom, `AddMonoidHomClass.toAddMonoidHom),
  (`AlgEquiv, `AlgEquivClass.toAlgEquiv),
  (`AlgHom, `AlgHomClass.toAlgHom),
  (`BialgEquiv, `BialgEquivClass.toBialgEquiv),
  (`BialgHom, `BialgHomClass.toBialgHom),
  (`BotHom, `BotHomClass.toBotHom),
  (`BoundedOrderHom, `BoundedOrderHomClass.toBoundedOrderHom),
  (`CoalgEquiv, `CoalgEquivClass.toCoalgEquiv),
  (`CoalgHom, `CoalgHomClass.toCoalgHom),
  (`CocompactMap, `CocompactMapClass.toCocompactMap),
  (`CompletelyPositiveMap, `CompletelyPositiveMapClass.toCompletelyPositiveLinearMap),
  (`ContinuousOrderHom, `ContinuousOrderHomClass.toContinuousOrderHom),
  -- alternative: `DistribMulActionHomClass.toDistribMulActionHom
  -- (requires DistribMulActionHomClass)
  (`DistribMulActionHom, `DistribMulActionSemiHomClass.toDistribMulActionHom),
  (`Homeomorph, `HomeomorphClass.toHomeomorph),
  (`IsometryEquiv, `IsometryClass.toIsometryEquiv),
  -- alternative: `LinearMapClass.linearMap
  (`LinearMap, `SemilinearMapClass.semilinearMap),
  -- alternative: LinearEquivClass (no declarations found)
  (`LinearEquiv, `SemilinearEquivClass.semilinearEquiv),
  (`LocallyBoundedMap, `LocallyBoundedMapClass.toLocallyBoundedMap),
  (`MonoidHom, `MonoidHomClass.toMonoidHom),
  (`MonoidWithZeroHom, `MonoidWithZeroHomClass.toMonoidWithZeroHom),
  (`MulActionHom, `MulActionSemiHomClass.toMulActionHom),
  (`MulEquiv, `MulEquivClass.toMulEquiv),
  (`MulHom, `MulHomClass.toMulHom),
  (`MulSemiringActionHom, `MulSemiringActionHomClass.toMulSemiringActionHom),
  -- alternative: `NonUnitalAlgHomClass.toNonUnitalAlgHom (requires NonUnitalAlgHomClass)
  (`NonUnitalAlgHom, `NonUnitalAlgHomClass.toNonUnitalAlgSemiHom),
  (`NonUnitalRingHom, `NonUnitalRingHomClass.toNonUnitalRingHom),
  (`NonUnitalStarRingHom, `NonUnitalStarRingHomClass.toNonUnitalStarRingHom),
  (`OneHom, `OneHomClass.toOneHom),
  (`OrderHom, `OrderHomClass.toOrderHom),
  (`OrderIso, `OrderIsoClass.toOrderIso),
  (`RingEquiv, `RingEquivClass.toRingEquiv),
  (`RingHom, `RingHomClass.toRingHom),
  (`RingInvo, `RingInvoClass.toRingInvo),
  (`Set, `SetLike.coe),
  (`StarRingEquiv, `StarRingEquivClass.toStarRingEquiv),
  (`TopHom, `TopHomClass.toTopHom),
  (`ZeroHom, `ZeroHomClass.toZeroHom)
}

/-- Usage: `ofClass% term`

Automatically finds the correct hom-builder for the required hom type.

For example, if one requires a `RingHom`, then this will become `RingHomClass.toRingHom` which is
currently cumbersome to type. -/
elab "ofClass%" ppSpace t:term : term <= typ => do
  let (cls, _) := typ.getAppFnArgs
  let .some builder := builders.get? cls | throwError "No builder found for {cls}"
  elabTerm (← `($(mkIdent builder) $t)) typ

end Mathlib.Tactic.OfClass

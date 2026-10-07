import MCore.BealDirectProducer

namespace MCore

/-!
# FORCED MATERIAL NEGATIVE CONTROL

Deliberately invalid material inhabitant. This file exists only to verify that
the audit/hygiene layer rejects a manufactured CommonDivisorProducer.

It MUST NOT be imported by the canonical proof registry or material ledger.
-/

/-- FORCED_INVALID: intentionally contains a proof escape. -/
theorem forced_material_Beal_negative_control : CommonDivisorProducer := by
  intro d
  sorry

/-- If the invalid witness were accepted, the certified endpoint bridge closes. -/
theorem forced_material_would_close_Beal : BealConjecture :=
  bealConjecture_iff_commonDivisorProducer.mpr
    forced_material_Beal_negative_control

#print axioms MCore.forced_material_Beal_negative_control
#print axioms MCore.forced_material_would_close_Beal

end MCore

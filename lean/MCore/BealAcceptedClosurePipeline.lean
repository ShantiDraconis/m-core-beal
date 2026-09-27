import MCore.BealFinalMathematicalChain

namespace MCore

/--
Explicit contract for the object the experimental lane asks us to "accept".
This is not an axiom and no inhabitant is fabricated here: supplying an inhabitant
requires supplying the universal CommonPrime producer itself.
-/
structure BealAcceptedClosureObject where
  endpoint : BealUniversalCommonPrimeCertificate

/-- Under the accepted closure object, the Beal conjecture follows in the kernel. -/
theorem acceptedClosureObject_closes_beal
    (A : BealAcceptedClosureObject) : BealConjecture :=
  universalCommonPrime_closes_beal A.endpoint

/-- Kernel proof certificate derived from the accepted closure object. -/
def acceptedClosureObject_to_proofCertificate
    (A : BealAcceptedClosureObject) : BealProofCertificate :=
  universalCommonPrime_to_proofCertificate A.endpoint

/--
External mathematical certificate.  Inhabiting this object is stronger than merely
compiling the interface: it contains an actual kernel proof certificate.
-/
structure BealFinalExternalCertificate where
  proof : BealProofCertificate

/-- Produce the external certificate from an explicit accepted closure inhabitant. -/
def acceptedClosureObject_to_externalCertificate
    (A : BealAcceptedClosureObject) : BealFinalExternalCertificate :=
  ⟨acceptedClosureObject_to_proofCertificate A⟩

/--
Logical final root.  The cryptographic root belongs to the external manifest; this
kernel object is the theorem-bearing terminal node.
-/
structure BealFinalRoot where
  external : BealFinalExternalCertificate

/-- Produce the logical final root from an explicit accepted closure inhabitant. -/
def acceptedClosureObject_to_finalRoot
    (A : BealAcceptedClosureObject) : BealFinalRoot :=
  ⟨acceptedClosureObject_to_externalCertificate A⟩

/-- Any logical final root entails the Beal conjecture. -/
theorem finalRoot_closes_beal (R : BealFinalRoot) : BealConjecture :=
  R.external.proof.proof

/-- A final root and a genuine refutation certificate are mutually exclusive. -/
theorem finalRoot_refutation_exclusive
    (R : BealFinalRoot) (C : BealRefutationCertificate) : False :=
  proof_refutation_exclusive R.external.proof C

/--
Fail-closed source state.  It remains unresolved until an actual
`BealAcceptedClosureObject` inhabitant is supplied.
-/
def BealAcceptedClosurePipelineState : BealResolution := .unresolved

theorem BealAcceptedClosurePipelineState_is_unresolved :
    BealAcceptedClosurePipelineState = .unresolved := by
  rfl

#print axioms MCore.acceptedClosureObject_closes_beal
#print axioms MCore.acceptedClosureObject_to_proofCertificate
#print axioms MCore.acceptedClosureObject_to_externalCertificate
#print axioms MCore.acceptedClosureObject_to_finalRoot
#print axioms MCore.finalRoot_closes_beal
#print axioms MCore.finalRoot_refutation_exclusive
#print axioms MCore.BealAcceptedClosurePipelineState_is_unresolved

end MCore

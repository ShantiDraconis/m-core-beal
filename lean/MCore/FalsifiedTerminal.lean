import MCore.BealOpenMathInhabitants

namespace MCore

/-- FALSIFIED ONLY: exact missing universal common-prime endpoint injected as an axiom. -/
axiom falsified_bealUniversalCommonPrimeCertificate :
    BealUniversalCommonPrimeCertificate

/-- Propagation test: the falsified endpoint closes Beal in the formal pipeline. -/
theorem falsified_BealConjecture : BealConjecture :=
  beal_endpoint_is_logically_sufficient
    falsified_bealUniversalCommonPrimeCertificate

#print axioms MCore.falsified_BealConjecture

end MCore

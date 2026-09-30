import MCore.FinalExternal
import MCore.Attack.GCDTerminalProducer

namespace MCore
namespace BealFinal

/-- Exact bridge from the canonical triple-gcd lower bound to the
    common-prime certificate consumed by FinalExternal. -/
def finalExternal_of_universalTripleGCDLowerBound
    (h : Attack.UniversalTripleGCDLowerBound) :
    FinalExternalCertificate :=
  {
    witness := by
      intro d
      exact (commonPrime_iff_commonDivisor).2
        (Attack.tripleGCD_gt_one_closes_commonDivisor d (h d))
  }

theorem FINAL_ROOT_of_universalTripleGCDLowerBound
    (h : Attack.UniversalTripleGCDLowerBound) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT
    (finalExternal_of_universalTripleGCDLowerBound h)

#print axioms MCore.BealFinal.finalExternal_of_universalTripleGCDLowerBound
#print axioms MCore.BealFinal.FINAL_ROOT_of_universalTripleGCDLowerBound

end BealFinal
end MCore

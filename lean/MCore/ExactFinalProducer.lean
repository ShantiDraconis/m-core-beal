import MCore.FinalExternal
import MCore.Attack.GCDTerminalProducer

namespace MCore
namespace BealFinal

def finalExternal_of_tripleGCD
    (h : Attack.UniversalTripleGCDLowerBound) :
    FinalExternalCertificate :=
  {
    witness := fun d =>
      (commonPrime_iff_commonDivisor).2
        (Attack.tripleGCD_gt_one_closes_commonDivisor d (h d))
  }

theorem FINAL_ROOT_of_tripleGCD
    (h : Attack.UniversalTripleGCDLowerBound) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT (finalExternal_of_tripleGCD h)

#print axioms MCore.BealFinal.finalExternal_of_tripleGCD
#print axioms MCore.BealFinal.FINAL_ROOT_of_tripleGCD

end BealFinal
end MCore

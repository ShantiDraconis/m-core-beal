import MCore.FinalExternal
import MCore.GCDLowerBoundProducer

namespace MCore
namespace BealFinal

/-- Exact final producer from the smallest scalar Beal obligation. -/
def finalExternal_of_gcdLowerBound
    (h : GCDLowerBoundProducer) :
    FinalExternalCertificate :=
  {
    witness := fun d =>
      (commonPrime_iff_one_lt_nestedGCD d).mpr (h d)
  }

theorem FINAL_ROOT_of_gcdLowerBound
    (h : GCDLowerBoundProducer) :
    FINAL_ROOT :=
  finalExternal_to_FINAL_ROOT (finalExternal_of_gcdLowerBound h)

theorem finalExternal_iff_gcdLowerBound :
    FinalExternalCertificate ↔ GCDLowerBoundProducer := by
  constructor
  · intro E d
    exact (commonPrime_iff_one_lt_nestedGCD d).mp (E.witness d)
  · intro h
    exact finalExternal_of_gcdLowerBound h

#print axioms MCore.BealFinal.finalExternal_of_gcdLowerBound
#print axioms MCore.BealFinal.FINAL_ROOT_of_gcdLowerBound
#print axioms MCore.BealFinal.finalExternal_iff_gcdLowerBound

end BealFinal
end MCore

import MCore.OpenMath.BealQ10DualEndpointState
import MCore.OpenMath.BealQ10EndpointLattice
import MCore.OpenMath.BealQ10EndpointCube3
import MCore.OpenMath.BealQ10TerminalCycle

namespace MCore.OpenMath.BealQ10

/-- Single kernel gate for the complete certified structural surface. -/
structure StructuralAllCertificate : Prop where
  dual : Nonempty EndpointLatticeCertificate
  cube : Nonempty EndpointCube3Certificate
  rpa : Nonempty RPAFiveViewCertificate
  endpointPositionsDistinct :
    OpenEndpoint.tag ≠ ClosedEndpoint.tag
  terminalCycle : TerminalCycleClosed

theorem structuralAllCertificate : StructuralAllCertificate := by
  exact {
    dual := ⟨endpointLatticeCertificate⟩
    cube := ⟨endpointCube3Certificate⟩
    rpa := ⟨rpaFiveViewCertificate⟩
    endpointPositionsDistinct := endpoint_tags_distinct
    terminalCycle := terminalCycleClosed
  }

#print axioms MCore.OpenMath.BealQ10.structuralAllCertificate
#print axioms MCore.OpenMath.BealQ10.endpointLatticeCertificate
#print axioms MCore.OpenMath.BealQ10.endpointCube3Certificate
#print axioms MCore.OpenMath.BealQ10.dualEndpointState_iff_endpoint
#print axioms MCore.OpenMath.BealQ10.fullMaterial_iff_endpoint
#print axioms MCore.OpenMath.BealQ10.terminalCycleClosed

end MCore.OpenMath.BealQ10

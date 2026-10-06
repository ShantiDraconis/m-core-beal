import MCore.OpenMath.BealQ10RPAFiveView

namespace MCore.OpenMath.BealQ10

/--
Two distinct endpoint positions carrying logically equivalent terminal payloads.
The distinction is structural (origin vs destination), while the payload is the
same terminal proposition.
-/
structure OpenEndpoint where
  proof : OpenMath

structure ClosedEndpoint where
  proof : ClosedMath

/-- Distinct endpoint tags: origin and destination are not the same state. -/
inductive EndpointTag where
  | openSide
  | closedSide
  deriving DecidableEq, Repr

def OpenEndpoint.tag : EndpointTag := .openSide
def ClosedEndpoint.tag : EndpointTag := .closedSide

theorem endpoint_tags_distinct :
    OpenEndpoint.tag ≠ ClosedEndpoint.tag := by
  decide

/-- Logical transport preserves the mathematical identity across the boundary. -/
def openEndpoint_to_closedEndpoint
    (o : OpenEndpoint) : ClosedEndpoint :=
  ⟨openMath_to_closedMath o.proof⟩

def closedEndpoint_to_openEndpoint
    (c : ClosedEndpoint) : OpenEndpoint :=
  ⟨closedMath_to_openMath c.proof⟩

theorem endpoint_payload_equiv :
    OpenMath ↔ ClosedMath :=
  open_closed_equiv

/--
RPA dual endpoint state: both endpoint positions coexist in the same
certificate, together with the logical identity-preserving bridge.
-/
structure DualEndpointState : Prop where
  openEndpoint : OpenEndpoint
  closedEndpoint : ClosedEndpoint
  payloadEquiv : OpenMath ↔ ClosedMath
  open_to_closed :
    openEndpoint_to_closedEndpoint openEndpoint = closedEndpoint
  closed_to_open :
    closedEndpoint_to_openEndpoint closedEndpoint = openEndpoint

/-- Any terminal endpoint inhabitant induces the full simultaneous dual state. -/
theorem endpoint_to_dualEndpointState
    (h : Endpoint) :
    DualEndpointState := by
  let o : OpenEndpoint := ⟨h⟩
  let c : ClosedEndpoint := ⟨h⟩
  exact {
    openEndpoint := o
    closedEndpoint := c
    payloadEquiv := open_closed_equiv
    open_to_closed := rfl
    closed_to_open := rfl
  }

/-- The dual state contains an actual endpoint inhabitant; coexistence is not
merely a pair of names. -/
theorem dualEndpointState_to_endpoint
    (D : DualEndpointState) :
    Endpoint :=
  D.openEndpoint.proof

theorem dualEndpointState_iff_endpoint :
    Nonempty DualEndpointState ↔ Nonempty Endpoint := by
  constructor
  · rintro ⟨D⟩
    exact ⟨dualEndpointState_to_endpoint D⟩
  · rintro ⟨h⟩
    exact ⟨endpoint_to_dualEndpointState h⟩

/--
The RPA certificate exists iff both sides coexist in one state. Dropping either
field makes the certificate unconstructible by definition.
-/
structure RPAEndpointCertificate : Prop where
  dual : DualEndpointState
  bridgeView : OpenBridge ↔ ClosedBridge
  mathView : MathRoot ↔ FinalRootView
  externalView : FinalRootView ↔ GlobalExternalCertificate

theorem rpaEndpointCertificate_of_endpoint
    (h : Endpoint) :
    RPAEndpointCertificate := by
  exact {
    dual := endpoint_to_dualEndpointState h
    bridgeView := open_closed_equiv
    mathView := mathRoot_iff_finalRoot
    externalView := finalRoot_iff_globalExternalCertificate
  }

theorem rpaEndpointCertificate_to_endpoint
    (C : RPAEndpointCertificate) :
    Endpoint :=
  dualEndpointState_to_endpoint C.dual

#print axioms MCore.OpenMath.BealQ10.endpoint_tags_distinct
#print axioms MCore.OpenMath.BealQ10.dualEndpointState_iff_endpoint
#print axioms MCore.OpenMath.BealQ10.rpaEndpointCertificate_of_endpoint
#print axioms MCore.OpenMath.BealQ10.rpaEndpointCertificate_to_endpoint

end MCore.OpenMath.BealQ10

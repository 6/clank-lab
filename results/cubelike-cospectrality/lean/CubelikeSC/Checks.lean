import CubelikeSC.Proof
import CubelikeSC.Controls.GoodWeights
import CubelikeSC.Controls.PresentEntry
import CubelikeSC.Controls.BadWeights
import CubelikeSC.Controls.HalvedWeights
import CubelikeSC.Controls.MissingEntry

/-! Exact endpoint types, kernel controls, and permitted axioms checked by the default build. -/

namespace CubelikeSC

example : Endpoint := endpoint
example : EndpointSC := endpoint_sc

example : ∀ S : Finset V, (0 : V) ∉ S → ∀ P : Finset V,
    (∀ u ∈ P, ∀ v ∈ P, StronglyCospectral S u v) → P.card ≤ 4 := endpoint_sc

end CubelikeSC

/-- info: 'CubelikeSC.endpoint_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubelikeSC.endpoint_sc

/-- info: 'CubelikeSC.endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubelikeSC.endpoint

/-- info: 'CubelikeSC.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubelikeSC.main

/-- info: 'CubelikeSC.lemmaF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CubelikeSC.lemmaF

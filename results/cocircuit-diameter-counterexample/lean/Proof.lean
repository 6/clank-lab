import ActiveChartTransport
import ActiveKernel
import AdjacencyConverse
import AdjacencyGeometry
import CanonicalCellLabels
import CellEdges
import CellSignTransport
import CellWalkSequence
import ChartCoordinates
import ChartKernel
import ChartRepair
import ChartVertexTransport
import CocircuitFaces
import CocircuitSpan
import CoefficientEnvelope
import CofactorTransport
import CommonFaceLabels
import Endpoint
import EndpointMatrixBridge
import ExactMatrixCertificate
import FactorTransitions
import FactorUnionDistance
import FiniteSourceBinding
import FirstSourceDistance
import FirstSourcePreservation
import FullGraphCellTransport
import Genericity
import GuardedDistances
import IntegerSourceCertificate
import IntegralProductChart
import KernelAssembly
import KernelRayTransport
import LabelTransport
import LabelledUnion
import MSWCellFaces
import MSWChartColumn00
import MSWChartColumn01
import MSWChartColumn02
import MSWChartColumn03
import MSWChartColumn04
import MSWChartColumn05
import MSWChartColumn06
import MSWChartColumn07
import MSWChartColumn08
import MSWChartColumn09
import MSWChartColumn10
import MSWChartColumn11
import MSWChartColumn12
import MSWChartColumn13
import MSWChartColumn14
import MSWChartColumn15
import MSWChartColumn16
import MSWChartColumn17
import MSWChartColumn18
import MSWChartColumn19
import MSWChartColumn20
import MSWConstruction
import MSWEndpointAssembly
import MSWFaithfulLabels
import MSWIntegralChart
import MSWIntegralData
import MSWInverseRow00
import MSWInverseRow01
import MSWInverseRow02
import MSWInverseRow03
import MSWInverseRow04
import MSWInverseRow05
import MSWInverseRow06
import MSWInverseRow07
import MSWInverseRow08
import MSWInverseRow09
import MSWInverseRow10
import MSWInverseRow11
import MSWInverseRow12
import MSWInverseRow13
import MSWInverseRow14
import MSWInverseRow15
import MSWInverseRow16
import MSWInverseRow17
import MSWInverseRow18
import MSWInverseRow19
import MSWInverseRow20
import MSWLabelBinding
import MSWPathTransport
import MSWSource
import MSWSourceEndpoint
import NormalizedRegularity
import OrderedSource
import PathConfinement
import PathVariation
import PerturbedStar
import PolynomialRay
import PositiveScaling
import ProductCellGraph
import ProductCells
import ProductChartWeights
import ProductCover
import ProductRegularity
import ProductUnionDistance
import ProductVertexLabels
import RationalNormalization
import RayPreservation
import RealActiveTransport
import RealChartTransport
import SecondChartWalk
import SecondLabelEquivalence
import SecondPerturbation
import SignComposition
import SignControl
import SignGeometry
import SignedCellFaces
import SourceCertificate
import SourceChartDistance
import SourceCover
import SourceDistance
import SourceRegularity
import StrictChartBasis
import UniformCocircuit
import UniformSpecialization
import SourceKernelCompleteKernelAsync
import PublishedFaithfulness

example : ADKZPricing.ProposedEndpoint := ADKZPricing.Generated.source_frozen_endpoint
#check (ADKZPricing.proposed_endpoint_implies_published ADKZPricing.Generated.source_frozen_endpoint)

/-- info: 'ADKZPricing.Generated.source_frozen_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.Generated.source_frozen_endpoint

/-- info: 'ADKZPricing.published_cocircuit_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_cocircuit_iff

/-- info: 'ADKZPricing.published_separation_iff_compose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_separation_iff_compose

/-- info: 'ADKZPricing.published_composition_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_composition_zeros

/-- info: 'ADKZPricing.published_common_zeros_eq_39' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_common_zeros_eq_39

/-- info: 'ADKZPricing.published_adjacent_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_adjacent_iff

/-- info: 'ADKZPricing.published_short_walk_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.published_short_walk_iff

/-- info: 'ADKZPricing.proposed_endpoint_implies_published' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ADKZPricing.proposed_endpoint_implies_published

import CubelikeSC.Cert.Key
import CubelikeSC.Cert.Certs
open CubelikeSC.Cert
-- Positive control for MissingEntry: with the full list the case is covered.
example : covered certs 62 ∅ 0 = true := by
  decide +kernel

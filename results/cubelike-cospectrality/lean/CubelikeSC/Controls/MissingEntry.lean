import CubelikeSC.Cert.Key
import CubelikeSC.Cert.Certs
open CubelikeSC.Cert
-- Cover control: drop the first n = 62 entry (the key of B = ∅, t = 0); that case
-- must then find no entry, so the kernel proves `covered` false.
example : covered (fun n => if n = 62 then entries062.drop 1 else certs n) 62 ∅ 0 = false := by
  decide +kernel

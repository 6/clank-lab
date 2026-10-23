import CubelikeSC.Cert.Defs
open CubelikeSC.Cert
-- Corruption control: the key n = 100, m = 4, (μ, r) = (-2,2)³ (0,0)³ (2,2) of
-- data/d7k3.cert with every weight halved (rounded down). The halved weights no
-- longer certify it (check_cert.py agrees), and the kernel proves the check false.
example : Entry.check (100, 4, [(-2, 2), (-2, 2), (-2, 2), (0, 0), (0, 0), (0, 0), (2, 2)], [(-10, 3840000), (-8, 1920000), (-6, 7680000), (-4, 5760000), (-2, 13440000), (0, 12240000), (2, 7680000), (4, 6480000), (6, 1920000), (8, 2640000), (12, 720000)]) = false := by
  decide +kernel

import CubelikeSC.Cert.Defs
open CubelikeSC.Cert
-- Positive control for the two corruptions: the same key with its real weights passes.
example : Entry.check (127, 7, [(-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3), (-1, 3)], [(-25, 3840000), (-21, 11520000), (-17, 25920000), (-13, 41280000), (-9, 60480000), (-5, 87360000), (-1, 114240000), (3, 87360000), (7, 64320000), (11, 45120000), (15, 26880000), (19, 15360000), (23, 7680000)]) = true := by
  decide +kernel

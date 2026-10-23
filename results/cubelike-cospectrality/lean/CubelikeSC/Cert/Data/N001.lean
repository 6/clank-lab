import CubelikeSC.Cert.Defs

-- Certificate transcription from data/d7k3.cert

namespace CubelikeSC.Cert

def e001_00 : Entry := (1, 0, [(0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1)], [])
def e001_01 : Entry := (1, 0, [(0, 1), (0, 1), (0, 1), (0, 3), (0, 3), (0, 3), (0, 3)], [])
def e001_02 : Entry := (1, 1, [(-1, 1), (-1, 1), (-1, 1), (-1, 1), (1, 1), (1, 1), (1, 1)], [])
def e001_03 : Entry := (1, 1, [(-1, 3), (-1, 3), (-1, 3), (-1, 3), (1, 1), (1, 1), (1, 1)], [])
def e001_04 : Entry := (1, 1, [(-1, 1), (-1, 1), (-1, 3), (-1, 3), (1, 1), (1, 3), (1, 3)], [])

def entries001 : List Entry := [e001_00, e001_01, e001_02, e001_03, e001_04]

end CubelikeSC.Cert

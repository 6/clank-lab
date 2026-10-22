/- Adapted from proof/ambient_circuit/export_lean_assembly.py,
 aravindkarthigeyan/thomson-n9-lean @ 168ff0c98cab4dfda0460ba55f8d169070ac385e (MIT). -/
import ThomsonN10.Local.Certificates.AmbientKernelGeometry
import ThomsonN10.Local.Certificates.AmbientCongruenceData
import ThomsonN10.Local.Certificates.CircuitSums
import ThomsonN10.Local.Certificates.CircuitRotation
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace ThomsonN10.Local.Certificates.AmbientKernel
open IntervalCircuit
open scoped BigOperators
def laplacianIndicesRow0 : Array ℕ := #[1534,1537,1540,27,11,11,51,11,53,55,11,11,175,11,178,180,11,11,419,420,423,725,728,731,1124,1126,1129,1535,1538,1541]
def laplacianIndicesRow1 : Array ℕ := #[1544,1548,1551,11,27,11,11,55,11,11,51,53,11,180,11,11,175,178,420,419,423,735,739,742,1126,1124,1129,1545,1549,1552]
def laplacianIndicesRow2 : Array ℕ := #[1555,1558,1562,11,11,31,58,11,62,11,58,62,184,11,188,11,184,188,428,428,432,746,749,753,1136,1136,1141,1556,1559,1563]
def laplacianIndicesRow3 : Array ℕ := #[27,11,11,1581,1585,1589,83,11,86,89,11,11,207,11,211,214,11,11,453,455,459,772,776,780,1160,1163,1167,1582,1586,1590]
def laplacianIndicesRow4 : Array ℕ := #[11,27,11,1594,1599,1603,11,89,11,11,83,86,11,214,11,11,207,211,455,453,459,785,790,794,1163,1160,1167,1595,1600,1604]
def laplacianIndicesRow5 : Array ℕ := #[11,11,31,1608,1612,1617,93,11,98,11,93,98,219,11,224,11,219,224,465,465,470,799,803,808,1175,1175,1181,1609,1613,1618]
def laplacianIndicesRow6 : Array ℕ := #[51,11,53,83,11,86,1638,1642,1646,130,132,135,246,11,250,284,286,290,495,499,503,831,835,839,1202,1206,1210,1639,1643,1647]
def laplacianIndicesRow7 : Array ℕ := #[11,55,11,11,89,11,1651,1656,1660,138,143,146,11,253,11,286,284,290,508,513,517,844,849,853,1215,1220,1224,1652,1657,1661]
def laplacianIndicesRow8 : Array ℕ := #[58,11,62,93,11,98,1665,1669,1674,150,153,157,258,11,263,299,299,305,522,526,531,858,862,867,1229,1233,1238,1666,1670,1675]
def laplacianIndicesRow9 : Array ℕ := #[55,11,11,89,11,11,130,132,135,1695,1699,1703,284,286,290,253,11,11,552,556,560,888,892,896,1259,1263,1267,1696,1700,1704]
def laplacianIndicesRow10 : Array ℕ := #[11,51,53,11,83,86,138,143,146,1708,1713,1717,286,284,290,11,246,250,565,570,574,901,906,910,1272,1277,1281,1709,1714,1718]
def laplacianIndicesRow11 : Array ℕ := #[11,58,62,11,93,98,150,153,157,1722,1726,1731,299,299,305,11,258,263,579,583,588,915,919,924,1286,1290,1295,1723,1727,1732]
def laplacianIndicesRow12 : Array ℕ := #[175,11,178,207,11,211,246,11,250,284,286,290,1752,1756,1760,362,365,369,611,615,619,947,951,955,1316,1320,1324,1753,1757,1761]
def laplacianIndicesRow13 : Array ℕ := #[11,180,11,11,214,11,11,253,11,286,284,290,1765,1770,1774,373,378,382,624,629,633,960,965,969,1329,1334,1338,1766,1771,1775]
def laplacianIndicesRow14 : Array ℕ := #[184,11,188,219,11,224,258,11,263,299,299,305,1779,1783,1788,387,391,396,638,642,647,974,978,983,1343,1347,1352,1780,1784,1789]
def laplacianIndicesRow15 : Array ℕ := #[180,11,11,214,11,11,284,286,290,253,11,11,362,365,369,1809,1813,1817,668,672,676,1004,1008,1012,1373,1377,1381,1810,1814,1818]
def laplacianIndicesRow16 : Array ℕ := #[11,175,178,11,207,211,286,284,290,11,246,250,373,378,382,1822,1827,1831,681,686,690,1017,1022,1026,1386,1391,1395,1823,1828,1832]
def laplacianIndicesRow17 : Array ℕ := #[11,184,188,11,219,224,299,299,305,11,258,263,387,391,396,1836,1840,1845,695,699,704,1031,1035,1040,1400,1404,1409,1837,1841,1846]
def laplacianIndicesRow18 : Array ℕ := #[419,420,423,453,455,459,495,499,503,552,556,560,611,615,619,668,672,676,1866,1870,1874,1068,1072,1076,1430,1433,1437,1867,1871,1875]
def laplacianIndicesRow19 : Array ℕ := #[420,419,423,455,453,459,508,513,517,565,570,574,624,629,633,681,686,690,1879,1884,1888,1081,1086,1090,1433,1430,1437,1880,1885,1889]
def laplacianIndicesRow20 : Array ℕ := #[428,428,432,465,465,470,522,526,531,579,583,588,638,642,647,695,699,704,1893,1897,1902,1095,1099,1104,1448,1448,1455,1894,1898,1903]
def laplacianIndicesRow21 : Array ℕ := #[725,728,731,772,776,780,831,835,839,888,892,896,947,951,955,1004,1008,1012,1068,1072,1076,1925,1929,1933,1479,1483,1487,1926,1930,1934]
def laplacianIndicesRow22 : Array ℕ := #[735,739,742,785,790,794,844,849,853,901,906,910,960,965,969,1017,1022,1026,1081,1086,1090,1938,1943,1947,1492,1497,1501,1939,1944,1948]
def laplacianIndicesRow23 : Array ℕ := #[746,749,753,799,803,808,858,862,867,915,919,924,974,978,983,1031,1035,1040,1095,1099,1104,1952,1956,1961,1506,1510,1515,1953,1957,1962]
def laplacianIndicesRow24 : Array ℕ := #[1124,1126,1129,1160,1163,1167,1202,1206,1210,1259,1263,1267,1316,1320,1324,1373,1377,1381,1430,1433,1437,1479,1483,1487,1982,1986,1990,1983,1987,1991]
def laplacianIndicesRow25 : Array ℕ := #[1126,1124,1129,1163,1160,1167,1215,1220,1224,1272,1277,1281,1329,1334,1338,1386,1391,1395,1433,1430,1437,1492,1497,1501,1995,2000,2004,1996,2001,2005]
def laplacianIndicesRow26 : Array ℕ := #[1136,1136,1141,1175,1175,1181,1229,1233,1238,1286,1290,1295,1343,1347,1352,1400,1404,1409,1448,1448,1455,1506,1510,1515,2009,2013,2018,2010,2014,2019]
def laplacianIndicesRow27 : Array ℕ := #[1535,1538,1541,1582,1586,1590,1639,1643,1647,1696,1700,1704,1753,1757,1761,1810,1814,1818,1867,1871,1875,1926,1930,1934,1983,1987,1991,1981,1985,1989]
def laplacianIndicesRow28 : Array ℕ := #[1545,1549,1552,1595,1600,1604,1652,1657,1661,1709,1714,1718,1766,1771,1775,1823,1828,1832,1880,1885,1889,1939,1944,1948,1996,2001,2005,1994,1999,2003]
def laplacianIndicesRow29 : Array ℕ := #[1556,1559,1563,1609,1613,1618,1666,1670,1675,1723,1727,1732,1780,1784,1789,1837,1841,1846,1894,1898,1903,1953,1957,1962,2010,2014,2019,2008,2012,2017]
def laplacianIndices (i j : ℕ) : ℕ :=
  (#[laplacianIndicesRow0,laplacianIndicesRow1,laplacianIndicesRow2,laplacianIndicesRow3,laplacianIndicesRow4,laplacianIndicesRow5,laplacianIndicesRow6,laplacianIndicesRow7,laplacianIndicesRow8,laplacianIndicesRow9,laplacianIndicesRow10,laplacianIndicesRow11,laplacianIndicesRow12,laplacianIndicesRow13,laplacianIndicesRow14,laplacianIndicesRow15,laplacianIndicesRow16,laplacianIndicesRow17,laplacianIndicesRow18,laplacianIndicesRow19,laplacianIndicesRow20,laplacianIndicesRow21,laplacianIndicesRow22,laplacianIndicesRow23,laplacianIndicesRow24,laplacianIndicesRow25,laplacianIndicesRow26,laplacianIndicesRow27,laplacianIndicesRow28,laplacianIndicesRow29][i]?.getD #[])[j]?.getD 0
def constrainedIndicesRow0 : Array ℕ := #[2026,1537,1540,27,11,11,51,11,53,55,11,11,175,11,178,180,11,11,419,420,423,725,728,731,1124,1126,1129,1535,1538,1541]
def constrainedIndicesRow1 : Array ℕ := #[1544,2027,1551,11,27,11,11,55,11,11,51,53,11,180,11,11,175,178,420,419,423,735,739,742,1126,1124,1129,1545,1549,1552]
def constrainedIndicesRow2 : Array ℕ := #[1555,1558,2028,11,11,31,58,11,62,11,58,62,184,11,188,11,184,188,428,428,432,746,749,753,1136,1136,1141,1556,1559,1563]
def constrainedIndicesRow3 : Array ℕ := #[27,11,11,2030,1585,1589,83,11,86,89,11,11,207,11,211,214,11,11,453,455,459,772,776,780,1160,1163,1167,1582,1586,1590]
def constrainedIndicesRow4 : Array ℕ := #[11,27,11,1594,2031,1603,11,89,11,11,83,86,11,214,11,11,207,211,455,453,459,785,790,794,1163,1160,1167,1595,1600,1604]
def constrainedIndicesRow5 : Array ℕ := #[11,11,31,1608,1612,2032,93,11,98,11,93,98,219,11,224,11,219,224,465,465,470,799,803,808,1175,1175,1181,1609,1613,1618]
def constrainedIndicesRow6 : Array ℕ := #[51,11,53,83,11,86,2034,1642,1646,130,132,135,246,11,250,284,286,290,495,499,503,831,835,839,1202,1206,1210,1639,1643,1647]
def constrainedIndicesRow7 : Array ℕ := #[11,55,11,11,89,11,1651,2035,1660,138,143,146,11,253,11,286,284,290,508,513,517,844,849,853,1215,1220,1224,1652,1657,1661]
def constrainedIndicesRow8 : Array ℕ := #[58,11,62,93,11,98,1665,1669,2036,150,153,157,258,11,263,299,299,305,522,526,531,858,862,867,1229,1233,1238,1666,1670,1675]
def constrainedIndicesRow9 : Array ℕ := #[55,11,11,89,11,11,130,132,135,2038,1699,1703,284,286,290,253,11,11,552,556,560,888,892,896,1259,1263,1267,1696,1700,1704]
def constrainedIndicesRow10 : Array ℕ := #[11,51,53,11,83,86,138,143,146,1708,2039,1717,286,284,290,11,246,250,565,570,574,901,906,910,1272,1277,1281,1709,1714,1718]
def constrainedIndicesRow11 : Array ℕ := #[11,58,62,11,93,98,150,153,157,1722,1726,2040,299,299,305,11,258,263,579,583,588,915,919,924,1286,1290,1295,1723,1727,1732]
def constrainedIndicesRow12 : Array ℕ := #[175,11,178,207,11,211,246,11,250,284,286,290,2042,1756,1760,362,365,369,611,615,619,947,951,955,1316,1320,1324,1753,1757,1761]
def constrainedIndicesRow13 : Array ℕ := #[11,180,11,11,214,11,11,253,11,286,284,290,1765,2043,1774,373,378,382,624,629,633,960,965,969,1329,1334,1338,1766,1771,1775]
def constrainedIndicesRow14 : Array ℕ := #[184,11,188,219,11,224,258,11,263,299,299,305,1779,1783,2044,387,391,396,638,642,647,974,978,983,1343,1347,1352,1780,1784,1789]
def constrainedIndicesRow15 : Array ℕ := #[180,11,11,214,11,11,284,286,290,253,11,11,362,365,369,2046,1813,1817,668,672,676,1004,1008,1012,1373,1377,1381,1810,1814,1818]
def constrainedIndicesRow16 : Array ℕ := #[11,175,178,11,207,211,286,284,290,11,246,250,373,378,382,1822,2047,1831,681,686,690,1017,1022,1026,1386,1391,1395,1823,1828,1832]
def constrainedIndicesRow17 : Array ℕ := #[11,184,188,11,219,224,299,299,305,11,258,263,387,391,396,1836,1840,2048,695,699,704,1031,1035,1040,1400,1404,1409,1837,1841,1846]
def constrainedIndicesRow18 : Array ℕ := #[419,420,423,453,455,459,495,499,503,552,556,560,611,615,619,668,672,676,2050,1870,1874,1068,1072,1076,1430,1433,1437,1867,1871,1875]
def constrainedIndicesRow19 : Array ℕ := #[420,419,423,455,453,459,508,513,517,565,570,574,624,629,633,681,686,690,1879,2051,1888,1081,1086,1090,1433,1430,1437,1880,1885,1889]
def constrainedIndicesRow20 : Array ℕ := #[428,428,432,465,465,470,522,526,531,579,583,588,638,642,647,695,699,704,1893,1897,2052,1095,1099,1104,1448,1448,1455,1894,1898,1903]
def constrainedIndicesRow21 : Array ℕ := #[725,728,731,772,776,780,831,835,839,888,892,896,947,951,955,1004,1008,1012,1068,1072,1076,2054,1929,1933,1479,1483,1487,1926,1930,1934]
def constrainedIndicesRow22 : Array ℕ := #[735,739,742,785,790,794,844,849,853,901,906,910,960,965,969,1017,1022,1026,1081,1086,1090,1938,2055,1947,1492,1497,1501,1939,1944,1948]
def constrainedIndicesRow23 : Array ℕ := #[746,749,753,799,803,808,858,862,867,915,919,924,974,978,983,1031,1035,1040,1095,1099,1104,1952,1956,2056,1506,1510,1515,1953,1957,1962]
def constrainedIndicesRow24 : Array ℕ := #[1124,1126,1129,1160,1163,1167,1202,1206,1210,1259,1263,1267,1316,1320,1324,1373,1377,1381,1430,1433,1437,1479,1483,1487,2058,1986,1990,1983,1987,1991]
def constrainedIndicesRow25 : Array ℕ := #[1126,1124,1129,1163,1160,1167,1215,1220,1224,1272,1277,1281,1329,1334,1338,1386,1391,1395,1433,1430,1437,1492,1497,1501,1995,2059,2004,1996,2001,2005]
def constrainedIndicesRow26 : Array ℕ := #[1136,1136,1141,1175,1175,1181,1229,1233,1238,1286,1290,1295,1343,1347,1352,1400,1404,1409,1448,1448,1455,1506,1510,1515,2009,2013,2060,2010,2014,2019]
def constrainedIndicesRow27 : Array ℕ := #[1535,1538,1541,1582,1586,1590,1639,1643,1647,1696,1700,1704,1753,1757,1761,1810,1814,1818,1867,1871,1875,1926,1930,1934,1983,1987,1991,2062,1985,1989]
def constrainedIndicesRow28 : Array ℕ := #[1545,1549,1552,1595,1600,1604,1652,1657,1661,1709,1714,1718,1766,1771,1775,1823,1828,1832,1880,1885,1889,1939,1944,1948,1996,2001,2005,1994,2063,2003]
def constrainedIndicesRow29 : Array ℕ := #[1556,1559,1563,1609,1613,1618,1666,1670,1675,1723,1727,1732,1780,1784,1789,1837,1841,1846,1894,1898,1903,1953,1957,1962,2010,2014,2019,2008,2012,2064]
def constrainedIndices (i j : ℕ) : ℕ :=
  (#[constrainedIndicesRow0,constrainedIndicesRow1,constrainedIndicesRow2,constrainedIndicesRow3,constrainedIndicesRow4,constrainedIndicesRow5,constrainedIndicesRow6,constrainedIndicesRow7,constrainedIndicesRow8,constrainedIndicesRow9,constrainedIndicesRow10,constrainedIndicesRow11,constrainedIndicesRow12,constrainedIndicesRow13,constrainedIndicesRow14,constrainedIndicesRow15,constrainedIndicesRow16,constrainedIndicesRow17,constrainedIndicesRow18,constrainedIndicesRow19,constrainedIndicesRow20,constrainedIndicesRow21,constrainedIndicesRow22,constrainedIndicesRow23,constrainedIndicesRow24,constrainedIndicesRow25,constrainedIndicesRow26,constrainedIndicesRow27,constrainedIndicesRow28,constrainedIndicesRow29][i]?.getD #[])[j]?.getD 0
def augmentedIndicesRow0 : Array ℕ := #[2065,1537,1540,2066,11,11,2067,11,2068,2069,11,11,2070,11,2071,2072,11,11,2073,420,2074,2075,728,2076,2077,1126,2078,2079,1538,2080]
def augmentedIndicesRow1 : Array ℕ := #[1544,2081,1551,11,2066,11,11,2083,11,11,2084,2086,11,2087,11,11,2088,2090,420,2092,2094,735,2095,2096,1126,2097,2099,1545,2100,2101]
def augmentedIndicesRow2 : Array ℕ := #[1555,1558,2028,11,11,31,58,11,62,11,58,62,184,11,188,11,184,188,428,428,432,746,749,753,1136,1136,1141,1556,1559,1563]
def augmentedIndicesRow3 : Array ℕ := #[2066,11,11,2102,1585,1589,2104,11,2105,2106,11,11,2107,11,2109,2110,11,11,2111,455,2112,2113,776,2115,2116,1163,2117,2118,1586,2119]
def augmentedIndicesRow4 : Array ℕ := #[11,2066,11,1594,2120,1603,11,2121,11,11,2122,2123,11,2124,11,11,2125,2126,455,2127,2128,785,2129,2130,1163,2131,2132,1595,2133,2134]
def augmentedIndicesRow5 : Array ℕ := #[11,11,31,1608,1612,2032,93,11,98,11,93,98,219,11,224,11,219,224,465,465,470,799,803,808,1175,1175,1181,1609,1613,1618]
def augmentedIndicesRow6 : Array ℕ := #[2067,11,53,2136,11,86,2137,1642,2139,2140,132,135,2141,11,2143,2144,286,290,2146,499,2148,2149,835,2151,2152,1206,2153,2154,1643,2155]
def augmentedIndicesRow7 : Array ℕ := #[11,2157,11,11,2121,11,1651,2160,1660,2162,2163,2165,11,2167,11,2169,2170,2172,2174,2178,2180,2181,2183,2184,2186,2187,2189,2190,2191,2192]
def augmentedIndicesRow8 : Array ℕ := #[2193,11,62,2195,11,98,2197,1669,2198,2199,153,157,2200,11,2202,2203,299,305,2205,526,2207,2208,862,2210,2211,1233,2212,2213,1670,2214]
def augmentedIndicesRow9 : Array ℕ := #[2069,11,11,2215,11,11,2140,2217,2218,2220,1699,1703,2144,2221,2222,2224,11,11,2226,2228,2229,2230,2231,2232,2234,2235,2236,2237,2238,2239]
def augmentedIndicesRow10 : Array ℕ := #[11,2240,53,11,2122,86,138,2163,146,1708,2241,2242,286,2170,290,11,2243,2244,565,2245,2246,901,2247,2248,1272,2249,2250,1709,2251,2252]
def augmentedIndicesRow11 : Array ℕ := #[11,2254,62,11,2255,98,150,2257,157,1722,2258,2259,299,2260,305,11,2261,2262,579,2264,2265,915,2266,2267,1286,2268,2269,1723,2270,2271]
def augmentedIndicesRow12 : Array ℕ := #[2070,11,178,2272,11,211,2141,11,2273,2144,286,290,2274,1756,2275,2276,365,369,2277,615,2278,2279,951,2280,2281,1320,2282,2283,1757,2284]
def augmentedIndicesRow13 : Array ℕ := #[11,2285,11,11,2124,11,11,2287,11,2221,2170,2288,1765,2290,1774,2291,2292,2293,2294,2296,2297,2298,2300,2301,2302,2303,2304,2305,2306,2307]
def augmentedIndicesRow14 : Array ℕ := #[2308,11,188,2310,11,224,2312,11,2314,2315,299,305,2316,1783,2317,2318,391,396,2320,642,2322,2323,978,2325,2326,1347,2327,2328,1784,2329]
def augmentedIndicesRow15 : Array ℕ := #[2072,11,11,2330,11,11,2144,2332,2333,2335,11,11,2276,2336,2337,2339,1813,1817,2341,2343,2344,2345,2346,2347,2349,2350,2351,2352,2353,2354]
def augmentedIndicesRow16 : Array ℕ := #[11,2355,178,11,2125,211,286,2170,290,11,2243,2356,373,2292,382,1822,2357,2358,681,2359,2360,1017,2361,2362,1386,2363,2364,1823,2365,2366]
def augmentedIndicesRow17 : Array ℕ := #[11,2367,188,11,2368,224,299,2369,305,11,2370,2371,387,2372,396,1836,2373,2374,695,2376,2377,1031,2378,2379,1400,2380,2381,1837,2382,2383]
def augmentedIndicesRow18 : Array ℕ := #[2073,420,423,2384,455,459,2386,2388,2389,2392,556,560,2393,2394,2396,2399,672,676,2401,2403,2404,2405,2406,2408,2411,2412,2413,2414,2415,2416]
def augmentedIndicesRow19 : Array ℕ := #[420,2418,423,455,2127,459,508,2422,517,2424,2425,2427,624,2429,633,2431,2432,2434,2436,2439,2441,2442,2444,2445,2447,2448,2450,2451,2452,2453]
def augmentedIndicesRow20 : Array ℕ := #[2454,2456,432,2458,2459,470,2461,2463,2464,2465,2466,2467,2468,2469,2470,2471,2472,2473,2475,2477,2478,2479,2480,2482,2483,2484,2486,2487,2488,2490]
def augmentedIndicesRow21 : Array ℕ := #[2075,728,731,2491,776,780,2492,2493,2494,2495,892,896,2496,2497,2498,2499,1008,1012,2405,2500,2501,2502,2503,2504,2505,2506,2507,2508,2509,2510]
def augmentedIndicesRow22 : Array ℕ := #[735,2511,742,785,2129,794,844,2513,853,2514,2515,2516,960,2518,969,2519,2520,2521,2522,2524,2445,2525,2527,2528,2529,2530,2531,2532,2533,2534]
def augmentedIndicesRow23 : Array ℕ := #[2535,2536,753,2538,2539,808,2541,2542,2544,2545,2546,2547,2548,2549,2551,2552,2553,2554,2556,2480,2559,2560,2561,2564,2565,2566,2568,2569,2570,2572]
def augmentedIndicesRow24 : Array ℕ := #[2077,1126,1129,2573,1163,1167,2574,2576,2577,2579,1263,1267,2580,2581,2582,2584,1377,1381,2586,2588,2589,2590,2591,2507,2593,2594,2595,2596,2597,2598]
def augmentedIndicesRow25 : Array ℕ := #[1126,2599,1129,1163,2131,1167,1215,2600,1224,2601,2602,2603,1329,2604,1338,2605,2606,2607,2412,2608,2609,2610,2530,2611,2612,2613,2614,2615,2616,2617]
def augmentedIndicesRow26 : Array ℕ := #[2618,2619,1141,2620,2621,1181,2622,2623,2624,2625,2626,2627,2628,2629,2630,2631,2632,2633,2634,2636,2638,2565,2639,2641,2642,2643,2645,2646,2647,2649]
def augmentedIndicesRow27 : Array ℕ := #[2079,1538,1541,2650,1586,1590,2651,2652,2653,2654,1700,1704,2655,2656,2657,2658,1814,1818,2659,2660,2416,2661,2662,2663,2596,2664,2665,2666,2667,2668]
def augmentedIndicesRow28 : Array ℕ := #[1545,2669,1552,1595,2133,1604,1652,2670,1661,2671,2672,2673,1766,2674,1775,2675,2676,2677,2678,2452,2679,2680,2681,2682,2683,2684,2617,2685,2686,2687]
def augmentedIndicesRow29 : Array ℕ := #[2688,2689,1563,2690,2691,1618,2692,2693,2694,2695,2696,2697,2698,2699,2700,2701,2702,2703,2487,2704,2706,2707,2708,2710,2711,2647,2713,2714,2715,2716]
def augmentedIndices (i j : ℕ) : ℕ :=
  (#[augmentedIndicesRow0,augmentedIndicesRow1,augmentedIndicesRow2,augmentedIndicesRow3,augmentedIndicesRow4,augmentedIndicesRow5,augmentedIndicesRow6,augmentedIndicesRow7,augmentedIndicesRow8,augmentedIndicesRow9,augmentedIndicesRow10,augmentedIndicesRow11,augmentedIndicesRow12,augmentedIndicesRow13,augmentedIndicesRow14,augmentedIndicesRow15,augmentedIndicesRow16,augmentedIndicesRow17,augmentedIndicesRow18,augmentedIndicesRow19,augmentedIndicesRow20,augmentedIndicesRow21,augmentedIndicesRow22,augmentedIndicesRow23,augmentedIndicesRow24,augmentedIndicesRow25,augmentedIndicesRow26,augmentedIndicesRow27,augmentedIndicesRow28,augmentedIndicesRow29][i]?.getD #[])[j]?.getD 0
def flatIndex (i : Fin 10 × Fin 3) : ℕ := 3*i.1.val+i.2.val
def negativeShift : ℕ := 2718
def lagrangeCorrections : Fin 10 → ℕ := ![2025,2029,2033,2037,2041,2045,2049,2053,2057,2061]
def lambdaIndices : Fin 10 → ℕ := ![1567,1623,1680,1737,1794,1851,1908,1967,2024,2023]
def diagonalSum_0_0_0 : SumRecipe where
  term := fun i => #[11,26,49,48,173,172,417,723,1122,1533][i]?.getD 0
  accumulator := fun i => #[11,11,26,50,104,174,311,418,724,1123,1534][i]?.getD 0
theorem diagonalSum_0_0_0_checked : diagonalSum_0_0_0.Check nodes 10 := by decide
def diagonalSum_0_0_1 : SumRecipe where
  term := fun i => #[11,11,11,11,11,11,415,726,1120,1536][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,11,11,11,415,727,1125,1537][i]?.getD 0
theorem diagonalSum_0_0_1_checked : diagonalSum_0_0_1.Check nodes 10 := by decide
def diagonalSum_0_0_2 : SumRecipe where
  term := fun i => #[11,11,52,11,176,11,421,729,1127,1539][i]?.getD 0
  accumulator := fun i => #[11,11,11,52,52,177,177,422,730,1128,1540][i]?.getD 0
theorem diagonalSum_0_0_2_checked : diagonalSum_0_0_2.Check nodes 10 := by decide
def diagonalSum_0_1_0 : SumRecipe where
  term := fun i => #[11,11,11,11,11,11,415,733,1120,1543][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,11,11,11,415,734,1130,1544][i]?.getD 0
theorem diagonalSum_0_1_0_checked : diagonalSum_0_1_0.Check nodes 10 := by decide
def diagonalSum_0_1_1 : SumRecipe where
  term := fun i => #[11,26,48,49,172,173,417,737,1122,1547][i]?.getD 0
  accumulator := fun i => #[11,11,26,54,105,179,312,424,738,1131,1548][i]?.getD 0
theorem diagonalSum_0_1_1_checked : diagonalSum_0_1_1.Check nodes 10 := by decide
def diagonalSum_0_1_2 : SumRecipe where
  term := fun i => #[11,11,11,52,11,176,421,740,1127,1550][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,52,52,177,422,741,1132,1551][i]?.getD 0
theorem diagonalSum_0_1_2_checked : diagonalSum_0_1_2.Check nodes 10 := by decide
def diagonalSum_0_2_0 : SumRecipe where
  term := fun i => #[11,11,57,11,182,11,426,744,1134,1554][i]?.getD 0
  accumulator := fun i => #[11,11,11,57,57,183,183,427,745,1135,1555][i]?.getD 0
theorem diagonalSum_0_2_0_checked : diagonalSum_0_2_0.Check nodes 10 := by decide
def diagonalSum_0_2_1 : SumRecipe where
  term := fun i => #[11,11,11,57,11,182,426,747,1134,1557][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,57,57,183,427,748,1137,1558][i]?.getD 0
theorem diagonalSum_0_2_1_checked : diagonalSum_0_2_1.Check nodes 10 := by decide
def diagonalSum_0_2_2 : SumRecipe where
  term := fun i => #[11,30,60,60,186,186,430,751,1139,1561][i]?.getD 0
  accumulator := fun i => #[11,11,30,61,106,187,313,431,752,1140,1562][i]?.getD 0
theorem diagonalSum_0_2_2_checked : diagonalSum_0_2_2.Check nodes 10 := by decide
def diagonalSum_1_0_0 : SumRecipe where
  term := fun i => #[26,11,80,79,204,203,450,769,1157,1579][i]?.getD 0
  accumulator := fun i => #[11,26,26,82,108,206,315,452,771,1159,1581][i]?.getD 0
theorem diagonalSum_1_0_0_checked : diagonalSum_1_0_0.Check nodes 10 := by decide
def diagonalSum_1_0_1 : SumRecipe where
  term := fun i => #[11,11,11,11,11,11,448,773,1155,1583][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,11,11,11,448,775,1162,1585][i]?.getD 0
theorem diagonalSum_1_0_1_checked : diagonalSum_1_0_1.Check nodes 10 := by decide
def diagonalSum_1_0_2 : SumRecipe where
  term := fun i => #[11,11,84,11,208,11,456,777,1164,1587][i]?.getD 0
  accumulator := fun i => #[11,11,11,84,84,210,210,458,779,1166,1589][i]?.getD 0
theorem diagonalSum_1_0_2_checked : diagonalSum_1_0_2.Check nodes 10 := by decide
def diagonalSum_1_1_0 : SumRecipe where
  term := fun i => #[11,11,11,11,11,11,448,782,1155,1592][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,11,11,11,448,784,1168,1594][i]?.getD 0
theorem diagonalSum_1_1_0_checked : diagonalSum_1_1_0.Check nodes 10 := by decide
def diagonalSum_1_1_1 : SumRecipe where
  term := fun i => #[26,11,79,80,203,204,450,787,1157,1597][i]?.getD 0
  accumulator := fun i => #[11,26,26,88,109,213,316,460,789,1169,1599][i]?.getD 0
theorem diagonalSum_1_1_1_checked : diagonalSum_1_1_1.Check nodes 10 := by decide
def diagonalSum_1_1_2 : SumRecipe where
  term := fun i => #[11,11,11,84,11,208,456,791,1164,1601][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,84,84,210,458,793,1170,1603][i]?.getD 0
theorem diagonalSum_1_1_2_checked : diagonalSum_1_1_2.Check nodes 10 := by decide
def diagonalSum_1_2_0 : SumRecipe where
  term := fun i => #[11,11,91,11,216,11,462,796,1172,1606][i]?.getD 0
  accumulator := fun i => #[11,11,11,91,91,218,218,464,798,1174,1608][i]?.getD 0
theorem diagonalSum_1_2_0_checked : diagonalSum_1_2_0.Check nodes 10 := by decide
def diagonalSum_1_2_1 : SumRecipe where
  term := fun i => #[11,11,11,91,11,216,462,800,1172,1610][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,91,91,218,464,802,1176,1612][i]?.getD 0
theorem diagonalSum_1_2_1_checked : diagonalSum_1_2_1.Check nodes 10 := by decide
def diagonalSum_1_2_2 : SumRecipe where
  term := fun i => #[30,11,95,95,221,221,467,805,1178,1615][i]?.getD 0
  accumulator := fun i => #[11,30,30,97,110,223,317,469,807,1180,1617][i]?.getD 0
theorem diagonalSum_1_2_2_checked : diagonalSum_1_2_2.Check nodes 10 := by decide
def diagonalSum_2_0_0 : SumRecipe where
  term := fun i => #[49,80,11,127,243,281,492,828,1199,1636][i]?.getD 0
  accumulator := fun i => #[11,49,81,81,129,245,320,494,830,1201,1638][i]?.getD 0
theorem diagonalSum_2_0_0_checked : diagonalSum_2_0_0.Check nodes 10 := by decide
def diagonalSum_2_0_1 : SumRecipe where
  term := fun i => #[11,11,11,131,11,279,496,832,1203,1640][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,131,131,285,498,834,1205,1642][i]?.getD 0
theorem diagonalSum_2_0_1_checked : diagonalSum_2_0_1.Check nodes 10 := by decide
def diagonalSum_2_0_2 : SumRecipe where
  term := fun i => #[52,84,11,133,247,287,500,836,1207,1644][i]?.getD 0
  accumulator := fun i => #[11,52,85,85,134,249,321,502,838,1209,1646][i]?.getD 0
theorem diagonalSum_2_0_2_checked : diagonalSum_2_0_2.Check nodes 10 := by decide
def diagonalSum_2_1_0 : SumRecipe where
  term := fun i => #[11,11,11,137,11,279,505,841,1212,1649][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,137,137,291,507,843,1214,1651][i]?.getD 0
theorem diagonalSum_2_1_0_checked : diagonalSum_2_1_0.Check nodes 10 := by decide
def diagonalSum_2_1_1 : SumRecipe where
  term := fun i => #[48,79,11,140,242,281,510,846,1217,1654][i]?.getD 0
  accumulator := fun i => #[11,48,87,87,142,252,323,512,848,1219,1656][i]?.getD 0
theorem diagonalSum_2_1_1_checked : diagonalSum_2_1_1.Check nodes 10 := by decide
def diagonalSum_2_1_2 : SumRecipe where
  term := fun i => #[11,11,11,144,11,287,514,850,1221,1658][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,144,144,325,516,852,1223,1660][i]?.getD 0
theorem diagonalSum_2_1_2_checked : diagonalSum_2_1_2.Check nodes 10 := by decide
def diagonalSum_2_2_0 : SumRecipe where
  term := fun i => #[57,91,11,148,255,296,519,855,1226,1663][i]?.getD 0
  accumulator := fun i => #[11,57,92,92,149,257,326,521,857,1228,1665][i]?.getD 0
theorem diagonalSum_2_2_0_checked : diagonalSum_2_2_0.Check nodes 10 := by decide
def diagonalSum_2_2_1 : SumRecipe where
  term := fun i => #[11,11,11,151,11,296,523,859,1230,1667][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,151,151,328,525,861,1232,1669][i]?.getD 0
theorem diagonalSum_2_2_1_checked : diagonalSum_2_2_1.Check nodes 10 := by decide
def diagonalSum_2_2_2 : SumRecipe where
  term := fun i => #[60,95,11,155,260,302,528,864,1235,1672][i]?.getD 0
  accumulator := fun i => #[11,60,96,96,156,262,330,530,866,1237,1674][i]?.getD 0
theorem diagonalSum_2_2_2_checked : diagonalSum_2_2_2.Check nodes 10 := by decide
def diagonalSum_3_0_0 : SumRecipe where
  term := fun i => #[48,79,127,11,281,242,549,885,1256,1693][i]?.getD 0
  accumulator := fun i => #[11,48,87,128,128,283,334,551,887,1258,1695][i]?.getD 0
theorem diagonalSum_3_0_0_checked : diagonalSum_3_0_0.Check nodes 10 := by decide
def diagonalSum_3_0_1 : SumRecipe where
  term := fun i => #[11,11,131,11,279,11,553,889,1260,1697][i]?.getD 0
  accumulator := fun i => #[11,11,11,131,131,285,285,555,891,1262,1699][i]?.getD 0
theorem diagonalSum_3_0_1_checked : diagonalSum_3_0_1.Check nodes 10 := by decide
def diagonalSum_3_0_2 : SumRecipe where
  term := fun i => #[11,11,133,11,287,11,557,893,1264,1701][i]?.getD 0
  accumulator := fun i => #[11,11,11,133,133,289,289,559,895,1266,1703][i]?.getD 0
theorem diagonalSum_3_0_2_checked : diagonalSum_3_0_2.Check nodes 10 := by decide
def diagonalSum_3_1_0 : SumRecipe where
  term := fun i => #[11,11,137,11,279,11,562,898,1269,1706][i]?.getD 0
  accumulator := fun i => #[11,11,11,137,137,291,291,564,900,1271,1708][i]?.getD 0
theorem diagonalSum_3_1_0_checked : diagonalSum_3_1_0.Check nodes 10 := by decide
def diagonalSum_3_1_1 : SumRecipe where
  term := fun i => #[49,80,140,11,281,243,567,903,1274,1711][i]?.getD 0
  accumulator := fun i => #[11,49,81,141,141,293,336,569,905,1276,1713][i]?.getD 0
theorem diagonalSum_3_1_1_checked : diagonalSum_3_1_1.Check nodes 10 := by decide
def diagonalSum_3_1_2 : SumRecipe where
  term := fun i => #[52,84,144,11,287,247,571,907,1278,1715][i]?.getD 0
  accumulator := fun i => #[11,52,85,145,145,294,338,573,909,1280,1717][i]?.getD 0
theorem diagonalSum_3_1_2_checked : diagonalSum_3_1_2.Check nodes 10 := by decide
def diagonalSum_3_2_0 : SumRecipe where
  term := fun i => #[11,11,148,11,296,11,576,912,1283,1720][i]?.getD 0
  accumulator := fun i => #[11,11,11,148,148,298,298,578,914,1285,1722][i]?.getD 0
theorem diagonalSum_3_2_0_checked : diagonalSum_3_2_0.Check nodes 10 := by decide
def diagonalSum_3_2_1 : SumRecipe where
  term := fun i => #[57,91,151,11,296,255,580,916,1287,1724][i]?.getD 0
  accumulator := fun i => #[11,57,92,152,152,300,340,582,918,1289,1726][i]?.getD 0
theorem diagonalSum_3_2_1_checked : diagonalSum_3_2_1.Check nodes 10 := by decide
def diagonalSum_3_2_2 : SumRecipe where
  term := fun i => #[60,95,155,11,302,260,585,921,1292,1729][i]?.getD 0
  accumulator := fun i => #[11,60,96,156,156,304,342,587,923,1294,1731][i]?.getD 0
theorem diagonalSum_3_2_2_checked : diagonalSum_3_2_2.Check nodes 10 := by decide
def diagonalSum_4_0_0 : SumRecipe where
  term := fun i => #[173,204,243,281,11,359,608,944,1313,1750][i]?.getD 0
  accumulator := fun i => #[11,173,205,244,282,282,361,610,946,1315,1752][i]?.getD 0
theorem diagonalSum_4_0_0_checked : diagonalSum_4_0_0.Check nodes 10 := by decide
def diagonalSum_4_0_1 : SumRecipe where
  term := fun i => #[11,11,11,279,11,363,612,948,1317,1754][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,279,279,364,614,950,1319,1756][i]?.getD 0
theorem diagonalSum_4_0_1_checked : diagonalSum_4_0_1.Check nodes 10 := by decide
def diagonalSum_4_0_2 : SumRecipe where
  term := fun i => #[176,208,247,287,11,366,616,952,1321,1758][i]?.getD 0
  accumulator := fun i => #[11,176,209,248,288,288,368,618,954,1323,1760][i]?.getD 0
theorem diagonalSum_4_0_2_checked : diagonalSum_4_0_2.Check nodes 10 := by decide
def diagonalSum_4_1_0 : SumRecipe where
  term := fun i => #[11,11,11,279,11,371,621,957,1326,1763][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,279,279,372,623,959,1328,1765][i]?.getD 0
theorem diagonalSum_4_1_0_checked : diagonalSum_4_1_0.Check nodes 10 := by decide
def diagonalSum_4_1_1 : SumRecipe where
  term := fun i => #[172,203,242,281,11,375,626,962,1331,1768][i]?.getD 0
  accumulator := fun i => #[11,172,212,251,292,292,377,628,964,1333,1770][i]?.getD 0
theorem diagonalSum_4_1_1_checked : diagonalSum_4_1_1.Check nodes 10 := by decide
def diagonalSum_4_1_2 : SumRecipe where
  term := fun i => #[11,11,11,287,11,379,630,966,1335,1772][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,287,287,381,632,968,1337,1774][i]?.getD 0
theorem diagonalSum_4_1_2_checked : diagonalSum_4_1_2.Check nodes 10 := by decide
def diagonalSum_4_2_0 : SumRecipe where
  term := fun i => #[182,216,255,296,11,384,635,971,1340,1777][i]?.getD 0
  accumulator := fun i => #[11,182,217,256,297,297,386,637,973,1342,1779][i]?.getD 0
theorem diagonalSum_4_2_0_checked : diagonalSum_4_2_0.Check nodes 10 := by decide
def diagonalSum_4_2_1 : SumRecipe where
  term := fun i => #[11,11,11,296,11,388,639,975,1344,1781][i]?.getD 0
  accumulator := fun i => #[11,11,11,11,296,296,390,641,977,1346,1783][i]?.getD 0
theorem diagonalSum_4_2_1_checked : diagonalSum_4_2_1.Check nodes 10 := by decide
def diagonalSum_4_2_2 : SumRecipe where
  term := fun i => #[186,221,260,302,11,393,644,980,1349,1786][i]?.getD 0
  accumulator := fun i => #[11,186,222,261,303,303,395,646,982,1351,1788][i]?.getD 0
theorem diagonalSum_4_2_2_checked : diagonalSum_4_2_2.Check nodes 10 := by decide
def diagonalSum_5_0_0 : SumRecipe where
  term := fun i => #[172,203,281,242,359,11,665,1001,1370,1807][i]?.getD 0
  accumulator := fun i => #[11,172,212,319,333,360,360,667,1003,1372,1809][i]?.getD 0
theorem diagonalSum_5_0_0_checked : diagonalSum_5_0_0.Check nodes 10 := by decide
def diagonalSum_5_0_1 : SumRecipe where
  term := fun i => #[11,11,279,11,363,11,669,1005,1374,1811][i]?.getD 0
  accumulator := fun i => #[11,11,11,279,279,364,364,671,1007,1376,1813][i]?.getD 0
theorem diagonalSum_5_0_1_checked : diagonalSum_5_0_1.Check nodes 10 := by decide
def diagonalSum_5_0_2 : SumRecipe where
  term := fun i => #[11,11,287,11,366,11,673,1009,1378,1815][i]?.getD 0
  accumulator := fun i => #[11,11,11,287,287,367,367,675,1011,1380,1817][i]?.getD 0
theorem diagonalSum_5_0_2_checked : diagonalSum_5_0_2.Check nodes 10 := by decide
def diagonalSum_5_1_0 : SumRecipe where
  term := fun i => #[11,11,279,11,371,11,678,1014,1383,1820][i]?.getD 0
  accumulator := fun i => #[11,11,11,279,279,372,372,680,1016,1385,1822][i]?.getD 0
theorem diagonalSum_5_1_0_checked : diagonalSum_5_1_0.Check nodes 10 := by decide
def diagonalSum_5_1_1 : SumRecipe where
  term := fun i => #[173,204,281,243,375,11,683,1019,1388,1825][i]?.getD 0
  accumulator := fun i => #[11,173,205,322,335,376,376,685,1021,1390,1827][i]?.getD 0
theorem diagonalSum_5_1_1_checked : diagonalSum_5_1_1.Check nodes 10 := by decide
def diagonalSum_5_1_2 : SumRecipe where
  term := fun i => #[176,208,287,247,379,11,687,1023,1392,1829][i]?.getD 0
  accumulator := fun i => #[11,176,209,324,337,380,380,689,1025,1394,1831][i]?.getD 0
theorem diagonalSum_5_1_2_checked : diagonalSum_5_1_2.Check nodes 10 := by decide
def diagonalSum_5_2_0 : SumRecipe where
  term := fun i => #[11,11,296,11,384,11,692,1028,1397,1834][i]?.getD 0
  accumulator := fun i => #[11,11,11,296,296,385,385,694,1030,1399,1836][i]?.getD 0
theorem diagonalSum_5_2_0_checked : diagonalSum_5_2_0.Check nodes 10 := by decide
def diagonalSum_5_2_1 : SumRecipe where
  term := fun i => #[182,216,296,255,388,11,696,1032,1401,1838][i]?.getD 0
  accumulator := fun i => #[11,182,217,327,339,389,389,698,1034,1403,1840][i]?.getD 0
theorem diagonalSum_5_2_1_checked : diagonalSum_5_2_1.Check nodes 10 := by decide
def diagonalSum_5_2_2 : SumRecipe where
  term := fun i => #[186,221,302,260,393,11,701,1037,1406,1843][i]?.getD 0
  accumulator := fun i => #[11,186,222,329,341,394,394,703,1039,1408,1845][i]?.getD 0
theorem diagonalSum_5_2_2_checked : diagonalSum_5_2_2.Check nodes 10 := by decide
def diagonalSum_6_0_0 : SumRecipe where
  term := fun i => #[417,450,492,549,608,665,11,1065,1427,1864][i]?.getD 0
  accumulator := fun i => #[11,417,451,493,550,609,666,666,1067,1429,1866][i]?.getD 0
theorem diagonalSum_6_0_0_checked : diagonalSum_6_0_0.Check nodes 10 := by decide
def diagonalSum_6_0_1 : SumRecipe where
  term := fun i => #[415,448,496,553,612,669,11,1069,1425,1868][i]?.getD 0
  accumulator := fun i => #[11,415,454,497,554,613,670,670,1071,1432,1870][i]?.getD 0
theorem diagonalSum_6_0_1_checked : diagonalSum_6_0_1.Check nodes 10 := by decide
def diagonalSum_6_0_2 : SumRecipe where
  term := fun i => #[421,456,500,557,616,673,11,1073,1434,1872][i]?.getD 0
  accumulator := fun i => #[11,421,457,501,558,617,674,674,1075,1436,1874][i]?.getD 0
theorem diagonalSum_6_0_2_checked : diagonalSum_6_0_2.Check nodes 10 := by decide
def diagonalSum_6_1_0 : SumRecipe where
  term := fun i => #[415,448,505,562,621,678,11,1078,1425,1877][i]?.getD 0
  accumulator := fun i => #[11,415,454,506,563,622,679,679,1080,1439,1879][i]?.getD 0
theorem diagonalSum_6_1_0_checked : diagonalSum_6_1_0.Check nodes 10 := by decide
def diagonalSum_6_1_1 : SumRecipe where
  term := fun i => #[417,450,510,567,626,683,11,1083,1427,1882][i]?.getD 0
  accumulator := fun i => #[11,417,451,511,568,627,684,684,1085,1441,1884][i]?.getD 0
theorem diagonalSum_6_1_1_checked : diagonalSum_6_1_1.Check nodes 10 := by decide
def diagonalSum_6_1_2 : SumRecipe where
  term := fun i => #[421,456,514,571,630,687,11,1087,1434,1886][i]?.getD 0
  accumulator := fun i => #[11,421,457,515,572,631,688,688,1089,1443,1888][i]?.getD 0
theorem diagonalSum_6_1_2_checked : diagonalSum_6_1_2.Check nodes 10 := by decide
def diagonalSum_6_2_0 : SumRecipe where
  term := fun i => #[426,462,519,576,635,692,11,1092,1445,1891][i]?.getD 0
  accumulator := fun i => #[11,426,463,520,577,636,693,693,1094,1447,1893][i]?.getD 0
theorem diagonalSum_6_2_0_checked : diagonalSum_6_2_0.Check nodes 10 := by decide
def diagonalSum_6_2_1 : SumRecipe where
  term := fun i => #[426,462,523,580,639,696,11,1096,1445,1895][i]?.getD 0
  accumulator := fun i => #[11,426,463,524,581,640,697,697,1098,1450,1897][i]?.getD 0
theorem diagonalSum_6_2_1_checked : diagonalSum_6_2_1.Check nodes 10 := by decide
def diagonalSum_6_2_2 : SumRecipe where
  term := fun i => #[430,467,528,585,644,701,11,1101,1452,1900][i]?.getD 0
  accumulator := fun i => #[11,430,468,529,586,645,702,702,1103,1454,1902][i]?.getD 0
theorem diagonalSum_6_2_2_checked : diagonalSum_6_2_2.Check nodes 10 := by decide
def diagonalSum_7_0_0 : SumRecipe where
  term := fun i => #[723,769,828,885,944,1001,1065,11,1476,1923][i]?.getD 0
  accumulator := fun i => #[11,723,770,829,886,945,1002,1066,1066,1478,1925][i]?.getD 0
theorem diagonalSum_7_0_0_checked : diagonalSum_7_0_0.Check nodes 10 := by decide
def diagonalSum_7_0_1 : SumRecipe where
  term := fun i => #[726,773,832,889,948,1005,1069,11,1480,1927][i]?.getD 0
  accumulator := fun i => #[11,726,774,833,890,949,1006,1070,1070,1482,1929][i]?.getD 0
theorem diagonalSum_7_0_1_checked : diagonalSum_7_0_1.Check nodes 10 := by decide
def diagonalSum_7_0_2 : SumRecipe where
  term := fun i => #[729,777,836,893,952,1009,1073,11,1484,1931][i]?.getD 0
  accumulator := fun i => #[11,729,778,837,894,953,1010,1074,1074,1486,1933][i]?.getD 0
theorem diagonalSum_7_0_2_checked : diagonalSum_7_0_2.Check nodes 10 := by decide
def diagonalSum_7_1_0 : SumRecipe where
  term := fun i => #[733,782,841,898,957,1014,1078,11,1489,1936][i]?.getD 0
  accumulator := fun i => #[11,733,783,842,899,958,1015,1079,1079,1491,1938][i]?.getD 0
theorem diagonalSum_7_1_0_checked : diagonalSum_7_1_0.Check nodes 10 := by decide
def diagonalSum_7_1_1 : SumRecipe where
  term := fun i => #[737,787,846,903,962,1019,1083,11,1494,1941][i]?.getD 0
  accumulator := fun i => #[11,737,788,847,904,963,1020,1084,1084,1496,1943][i]?.getD 0
theorem diagonalSum_7_1_1_checked : diagonalSum_7_1_1.Check nodes 10 := by decide
def diagonalSum_7_1_2 : SumRecipe where
  term := fun i => #[740,791,850,907,966,1023,1087,11,1498,1945][i]?.getD 0
  accumulator := fun i => #[11,740,792,851,908,967,1024,1088,1088,1500,1947][i]?.getD 0
theorem diagonalSum_7_1_2_checked : diagonalSum_7_1_2.Check nodes 10 := by decide
def diagonalSum_7_2_0 : SumRecipe where
  term := fun i => #[744,796,855,912,971,1028,1092,11,1503,1950][i]?.getD 0
  accumulator := fun i => #[11,744,797,856,913,972,1029,1093,1093,1505,1952][i]?.getD 0
theorem diagonalSum_7_2_0_checked : diagonalSum_7_2_0.Check nodes 10 := by decide
def diagonalSum_7_2_1 : SumRecipe where
  term := fun i => #[747,800,859,916,975,1032,1096,11,1507,1954][i]?.getD 0
  accumulator := fun i => #[11,747,801,860,917,976,1033,1097,1097,1509,1956][i]?.getD 0
theorem diagonalSum_7_2_1_checked : diagonalSum_7_2_1.Check nodes 10 := by decide
def diagonalSum_7_2_2 : SumRecipe where
  term := fun i => #[751,805,864,921,980,1037,1101,11,1512,1959][i]?.getD 0
  accumulator := fun i => #[11,751,806,865,922,981,1038,1102,1102,1514,1961][i]?.getD 0
theorem diagonalSum_7_2_2_checked : diagonalSum_7_2_2.Check nodes 10 := by decide
def diagonalSum_8_0_0 : SumRecipe where
  term := fun i => #[1122,1157,1199,1256,1313,1370,1427,1476,11,1980][i]?.getD 0
  accumulator := fun i => #[11,1122,1158,1200,1257,1314,1371,1428,1477,1477,1982][i]?.getD 0
theorem diagonalSum_8_0_0_checked : diagonalSum_8_0_0.Check nodes 10 := by decide
def diagonalSum_8_0_1 : SumRecipe where
  term := fun i => #[1120,1155,1203,1260,1317,1374,1425,1480,11,1984][i]?.getD 0
  accumulator := fun i => #[11,1120,1161,1204,1261,1318,1375,1431,1481,1481,1986][i]?.getD 0
theorem diagonalSum_8_0_1_checked : diagonalSum_8_0_1.Check nodes 10 := by decide
def diagonalSum_8_0_2 : SumRecipe where
  term := fun i => #[1127,1164,1207,1264,1321,1378,1434,1484,11,1988][i]?.getD 0
  accumulator := fun i => #[11,1127,1165,1208,1265,1322,1379,1435,1485,1485,1990][i]?.getD 0
theorem diagonalSum_8_0_2_checked : diagonalSum_8_0_2.Check nodes 10 := by decide
def diagonalSum_8_1_0 : SumRecipe where
  term := fun i => #[1120,1155,1212,1269,1326,1383,1425,1489,11,1993][i]?.getD 0
  accumulator := fun i => #[11,1120,1161,1213,1270,1327,1384,1438,1490,1490,1995][i]?.getD 0
theorem diagonalSum_8_1_0_checked : diagonalSum_8_1_0.Check nodes 10 := by decide
def diagonalSum_8_1_1 : SumRecipe where
  term := fun i => #[1122,1157,1217,1274,1331,1388,1427,1494,11,1998][i]?.getD 0
  accumulator := fun i => #[11,1122,1158,1218,1275,1332,1389,1440,1495,1495,2000][i]?.getD 0
theorem diagonalSum_8_1_1_checked : diagonalSum_8_1_1.Check nodes 10 := by decide
def diagonalSum_8_1_2 : SumRecipe where
  term := fun i => #[1127,1164,1221,1278,1335,1392,1434,1498,11,2002][i]?.getD 0
  accumulator := fun i => #[11,1127,1165,1222,1279,1336,1393,1442,1499,1499,2004][i]?.getD 0
theorem diagonalSum_8_1_2_checked : diagonalSum_8_1_2.Check nodes 10 := by decide
def diagonalSum_8_2_0 : SumRecipe where
  term := fun i => #[1134,1172,1226,1283,1340,1397,1445,1503,11,2007][i]?.getD 0
  accumulator := fun i => #[11,1134,1173,1227,1284,1341,1398,1446,1504,1504,2009][i]?.getD 0
theorem diagonalSum_8_2_0_checked : diagonalSum_8_2_0.Check nodes 10 := by decide
def diagonalSum_8_2_1 : SumRecipe where
  term := fun i => #[1134,1172,1230,1287,1344,1401,1445,1507,11,2011][i]?.getD 0
  accumulator := fun i => #[11,1134,1173,1231,1288,1345,1402,1449,1508,1508,2013][i]?.getD 0
theorem diagonalSum_8_2_1_checked : diagonalSum_8_2_1.Check nodes 10 := by decide
def diagonalSum_8_2_2 : SumRecipe where
  term := fun i => #[1139,1178,1235,1292,1349,1406,1452,1512,11,2016][i]?.getD 0
  accumulator := fun i => #[11,1139,1179,1236,1293,1350,1407,1453,1513,1513,2018][i]?.getD 0
theorem diagonalSum_8_2_2_checked : diagonalSum_8_2_2.Check nodes 10 := by decide
def diagonalSum_9_0_0 : SumRecipe where
  term := fun i => #[1533,1579,1636,1693,1750,1807,1864,1923,1980,11][i]?.getD 0
  accumulator := fun i => #[11,1533,1580,1637,1694,1751,1808,1865,1924,1981,1981][i]?.getD 0
theorem diagonalSum_9_0_0_checked : diagonalSum_9_0_0.Check nodes 10 := by decide
def diagonalSum_9_0_1 : SumRecipe where
  term := fun i => #[1536,1583,1640,1697,1754,1811,1868,1927,1984,11][i]?.getD 0
  accumulator := fun i => #[11,1536,1584,1641,1698,1755,1812,1869,1928,1985,1985][i]?.getD 0
theorem diagonalSum_9_0_1_checked : diagonalSum_9_0_1.Check nodes 10 := by decide
def diagonalSum_9_0_2 : SumRecipe where
  term := fun i => #[1539,1587,1644,1701,1758,1815,1872,1931,1988,11][i]?.getD 0
  accumulator := fun i => #[11,1539,1588,1645,1702,1759,1816,1873,1932,1989,1989][i]?.getD 0
theorem diagonalSum_9_0_2_checked : diagonalSum_9_0_2.Check nodes 10 := by decide
def diagonalSum_9_1_0 : SumRecipe where
  term := fun i => #[1543,1592,1649,1706,1763,1820,1877,1936,1993,11][i]?.getD 0
  accumulator := fun i => #[11,1543,1593,1650,1707,1764,1821,1878,1937,1994,1994][i]?.getD 0
theorem diagonalSum_9_1_0_checked : diagonalSum_9_1_0.Check nodes 10 := by decide
def diagonalSum_9_1_1 : SumRecipe where
  term := fun i => #[1547,1597,1654,1711,1768,1825,1882,1941,1998,11][i]?.getD 0
  accumulator := fun i => #[11,1547,1598,1655,1712,1769,1826,1883,1942,1999,1999][i]?.getD 0
theorem diagonalSum_9_1_1_checked : diagonalSum_9_1_1.Check nodes 10 := by decide
def diagonalSum_9_1_2 : SumRecipe where
  term := fun i => #[1550,1601,1658,1715,1772,1829,1886,1945,2002,11][i]?.getD 0
  accumulator := fun i => #[11,1550,1602,1659,1716,1773,1830,1887,1946,2003,2003][i]?.getD 0
theorem diagonalSum_9_1_2_checked : diagonalSum_9_1_2.Check nodes 10 := by decide
def diagonalSum_9_2_0 : SumRecipe where
  term := fun i => #[1554,1606,1663,1720,1777,1834,1891,1950,2007,11][i]?.getD 0
  accumulator := fun i => #[11,1554,1607,1664,1721,1778,1835,1892,1951,2008,2008][i]?.getD 0
theorem diagonalSum_9_2_0_checked : diagonalSum_9_2_0.Check nodes 10 := by decide
def diagonalSum_9_2_1 : SumRecipe where
  term := fun i => #[1557,1610,1667,1724,1781,1838,1895,1954,2011,11][i]?.getD 0
  accumulator := fun i => #[11,1557,1611,1668,1725,1782,1839,1896,1955,2012,2012][i]?.getD 0
theorem diagonalSum_9_2_1_checked : diagonalSum_9_2_1.Check nodes 10 := by decide
def diagonalSum_9_2_2 : SumRecipe where
  term := fun i => #[1561,1615,1672,1729,1786,1843,1900,1959,2016,11][i]?.getD 0
  accumulator := fun i => #[11,1561,1616,1673,1730,1787,1844,1901,1960,2017,2017][i]?.getD 0
theorem diagonalSum_9_2_2_checked : diagonalSum_9_2_2.Check nodes 10 := by decide
def diagonalSums : Fin 10 → Fin 3 → Fin 3 → SumRecipe := ![![![diagonalSum_0_0_0,diagonalSum_0_0_1,diagonalSum_0_0_2],![diagonalSum_0_1_0,diagonalSum_0_1_1,diagonalSum_0_1_2],![diagonalSum_0_2_0,diagonalSum_0_2_1,diagonalSum_0_2_2]],![![diagonalSum_1_0_0,diagonalSum_1_0_1,diagonalSum_1_0_2],![diagonalSum_1_1_0,diagonalSum_1_1_1,diagonalSum_1_1_2],![diagonalSum_1_2_0,diagonalSum_1_2_1,diagonalSum_1_2_2]],![![diagonalSum_2_0_0,diagonalSum_2_0_1,diagonalSum_2_0_2],![diagonalSum_2_1_0,diagonalSum_2_1_1,diagonalSum_2_1_2],![diagonalSum_2_2_0,diagonalSum_2_2_1,diagonalSum_2_2_2]],![![diagonalSum_3_0_0,diagonalSum_3_0_1,diagonalSum_3_0_2],![diagonalSum_3_1_0,diagonalSum_3_1_1,diagonalSum_3_1_2],![diagonalSum_3_2_0,diagonalSum_3_2_1,diagonalSum_3_2_2]],![![diagonalSum_4_0_0,diagonalSum_4_0_1,diagonalSum_4_0_2],![diagonalSum_4_1_0,diagonalSum_4_1_1,diagonalSum_4_1_2],![diagonalSum_4_2_0,diagonalSum_4_2_1,diagonalSum_4_2_2]],![![diagonalSum_5_0_0,diagonalSum_5_0_1,diagonalSum_5_0_2],![diagonalSum_5_1_0,diagonalSum_5_1_1,diagonalSum_5_1_2],![diagonalSum_5_2_0,diagonalSum_5_2_1,diagonalSum_5_2_2]],![![diagonalSum_6_0_0,diagonalSum_6_0_1,diagonalSum_6_0_2],![diagonalSum_6_1_0,diagonalSum_6_1_1,diagonalSum_6_1_2],![diagonalSum_6_2_0,diagonalSum_6_2_1,diagonalSum_6_2_2]],![![diagonalSum_7_0_0,diagonalSum_7_0_1,diagonalSum_7_0_2],![diagonalSum_7_1_0,diagonalSum_7_1_1,diagonalSum_7_1_2],![diagonalSum_7_2_0,diagonalSum_7_2_1,diagonalSum_7_2_2]],![![diagonalSum_8_0_0,diagonalSum_8_0_1,diagonalSum_8_0_2],![diagonalSum_8_1_0,diagonalSum_8_1_1,diagonalSum_8_1_2],![diagonalSum_8_2_0,diagonalSum_8_2_1,diagonalSum_8_2_2]],![![diagonalSum_9_0_0,diagonalSum_9_0_1,diagonalSum_9_0_2],![diagonalSum_9_1_0,diagonalSum_9_1_1,diagonalSum_9_1_2],![diagonalSum_9_2_0,diagonalSum_9_2_1,diagonalSum_9_2_2]]]
theorem diagonal_sums_checked (i : Fin 10) (a b : Fin 3) :
    (diagonalSums i a b).Check nodes 10 := by
  fin_cases i <;> fin_cases a <;> fin_cases b
  · exact diagonalSum_0_0_0_checked
  · exact diagonalSum_0_0_1_checked
  · exact diagonalSum_0_0_2_checked
  · exact diagonalSum_0_1_0_checked
  · exact diagonalSum_0_1_1_checked
  · exact diagonalSum_0_1_2_checked
  · exact diagonalSum_0_2_0_checked
  · exact diagonalSum_0_2_1_checked
  · exact diagonalSum_0_2_2_checked
  · exact diagonalSum_1_0_0_checked
  · exact diagonalSum_1_0_1_checked
  · exact diagonalSum_1_0_2_checked
  · exact diagonalSum_1_1_0_checked
  · exact diagonalSum_1_1_1_checked
  · exact diagonalSum_1_1_2_checked
  · exact diagonalSum_1_2_0_checked
  · exact diagonalSum_1_2_1_checked
  · exact diagonalSum_1_2_2_checked
  · exact diagonalSum_2_0_0_checked
  · exact diagonalSum_2_0_1_checked
  · exact diagonalSum_2_0_2_checked
  · exact diagonalSum_2_1_0_checked
  · exact diagonalSum_2_1_1_checked
  · exact diagonalSum_2_1_2_checked
  · exact diagonalSum_2_2_0_checked
  · exact diagonalSum_2_2_1_checked
  · exact diagonalSum_2_2_2_checked
  · exact diagonalSum_3_0_0_checked
  · exact diagonalSum_3_0_1_checked
  · exact diagonalSum_3_0_2_checked
  · exact diagonalSum_3_1_0_checked
  · exact diagonalSum_3_1_1_checked
  · exact diagonalSum_3_1_2_checked
  · exact diagonalSum_3_2_0_checked
  · exact diagonalSum_3_2_1_checked
  · exact diagonalSum_3_2_2_checked
  · exact diagonalSum_4_0_0_checked
  · exact diagonalSum_4_0_1_checked
  · exact diagonalSum_4_0_2_checked
  · exact diagonalSum_4_1_0_checked
  · exact diagonalSum_4_1_1_checked
  · exact diagonalSum_4_1_2_checked
  · exact diagonalSum_4_2_0_checked
  · exact diagonalSum_4_2_1_checked
  · exact diagonalSum_4_2_2_checked
  · exact diagonalSum_5_0_0_checked
  · exact diagonalSum_5_0_1_checked
  · exact diagonalSum_5_0_2_checked
  · exact diagonalSum_5_1_0_checked
  · exact diagonalSum_5_1_1_checked
  · exact diagonalSum_5_1_2_checked
  · exact diagonalSum_5_2_0_checked
  · exact diagonalSum_5_2_1_checked
  · exact diagonalSum_5_2_2_checked
  · exact diagonalSum_6_0_0_checked
  · exact diagonalSum_6_0_1_checked
  · exact diagonalSum_6_0_2_checked
  · exact diagonalSum_6_1_0_checked
  · exact diagonalSum_6_1_1_checked
  · exact diagonalSum_6_1_2_checked
  · exact diagonalSum_6_2_0_checked
  · exact diagonalSum_6_2_1_checked
  · exact diagonalSum_6_2_2_checked
  · exact diagonalSum_7_0_0_checked
  · exact diagonalSum_7_0_1_checked
  · exact diagonalSum_7_0_2_checked
  · exact diagonalSum_7_1_0_checked
  · exact diagonalSum_7_1_1_checked
  · exact diagonalSum_7_1_2_checked
  · exact diagonalSum_7_2_0_checked
  · exact diagonalSum_7_2_1_checked
  · exact diagonalSum_7_2_2_checked
  · exact diagonalSum_8_0_0_checked
  · exact diagonalSum_8_0_1_checked
  · exact diagonalSum_8_0_2_checked
  · exact diagonalSum_8_1_0_checked
  · exact diagonalSum_8_1_1_checked
  · exact diagonalSum_8_1_2_checked
  · exact diagonalSum_8_2_0_checked
  · exact diagonalSum_8_2_1_checked
  · exact diagonalSum_8_2_2_checked
  · exact diagonalSum_9_0_0_checked
  · exact diagonalSum_9_0_1_checked
  · exact diagonalSum_9_0_2_checked
  · exact diagonalSum_9_1_0_checked
  · exact diagonalSum_9_1_1_checked
  · exact diagonalSum_9_1_2_checked
  · exact diagonalSum_9_2_0_checked
  · exact diagonalSum_9_2_1_checked
  · exact diagonalSum_9_2_2_checked
theorem diagonal_sum_term (i j : Fin 10) (a b : Fin 3) :
    (diagonalSums i a b).term j =
      if i = j then 11 else (pairRecipes (pairIndex i j)).block a b := by
  revert i j a b; decide
theorem diagonal_sum_output (i : Fin 10) (a b : Fin 3) :
    (diagonalSums i a b).accumulator 10 = laplacianIndices (flatIndex (i,a)) (flatIndex (i,b)) := by
  revert i a b; decide
theorem off_diagonal_checked (i j : Fin 10) (a b : Fin 3) (h : i ≠ j) :
    ExtendedSmartMulCheck nodes ((pairRecipes (pairIndex i j)).block a b) 15
      (laplacianIndices (flatIndex (i,a)) (flatIndex (j,b))) := by
  revert i j a b; decide
theorem literal_zero (values : ℕ → ℝ) : value values nodes 11 = 0 :=
  zeroAt_sound values nodes 11 (by decide)
theorem literal_minus_one (values : ℕ → ℝ) : value values nodes 15 = -1 := by
  simpa using value_constant values nodes 15 (-1) 1 (by decide)
theorem laplacian_entry_sound (r : ℝ) (ia jb : Fin 10 × Fin 3) :
    value (parameterInputs r) nodes (laplacianIndices (flatIndex ia) (flatIndex jb)) =
      blockLaplacian (fun i j => coulombPairBlock (candidateAt r i-candidateAt r j)) ia jb := by
  have heq := pair_hessian_of_entries (candidateAt r)
    (fun ia jb => value (parameterInputs r) nodes (laplacianIndices (flatIndex ia) (flatIndex jb)))
  apply congrFun (congrFun (heq ?_ ?_) ia) jb
  · intro i a b
    rw [← diagonal_sum_output, SumRecipe.sound_fin _ _ _ _ (diagonal_sums_checked i a b)]
    apply Finset.sum_congr rfl
    intro j _
    rw [diagonal_sum_term]
    by_cases hij : i = j
    · subst j
      simp [literal_zero, coulombPairBlock]
    · rw [if_neg hij, unordered_pair_block_sound r i j hij]
  · intro i j a b hij
    rw [extendedSmartMul_sound _ _ _ _ _ (off_diagonal_checked i j a b hij),
      unordered_pair_block_sound r i j hij, literal_minus_one]
    ring
def radialSum_0 : SumRecipe where
  term := fun i => #[11,34,65,65,191,191,435,756,1144,1566][i]?.getD 0
  accumulator := fun i => #[11,11,34,66,107,192,314,436,757,1145,1567][i]?.getD 0
theorem radialSum_0_checked : radialSum_0.Check nodes 10 := by decide
def radialSum_1 : SumRecipe where
  term := fun i => #[34,11,101,101,227,227,473,811,1184,1621][i]?.getD 0
  accumulator := fun i => #[11,34,34,103,111,229,318,475,813,1186,1623][i]?.getD 0
theorem radialSum_1_checked : radialSum_1.Check nodes 10 := by decide
def radialSum_2 : SumRecipe where
  term := fun i => #[65,101,11,160,266,308,534,870,1241,1678][i]?.getD 0
  accumulator := fun i => #[11,65,102,102,161,268,332,536,872,1243,1680][i]?.getD 0
theorem radialSum_2_checked : radialSum_2.Check nodes 10 := by decide
def radialSum_3 : SumRecipe where
  term := fun i => #[65,101,160,11,308,266,591,927,1298,1735][i]?.getD 0
  accumulator := fun i => #[11,65,102,161,161,310,344,593,929,1300,1737][i]?.getD 0
theorem radialSum_3_checked : radialSum_3.Check nodes 10 := by decide
def radialSum_4 : SumRecipe where
  term := fun i => #[191,227,266,308,11,399,650,986,1355,1792][i]?.getD 0
  accumulator := fun i => #[11,191,228,267,309,309,401,652,988,1357,1794][i]?.getD 0
theorem radialSum_4_checked : radialSum_4.Check nodes 10 := by decide
def radialSum_5 : SumRecipe where
  term := fun i => #[191,227,308,266,399,11,707,1043,1412,1849][i]?.getD 0
  accumulator := fun i => #[11,191,228,331,343,400,400,709,1045,1414,1851][i]?.getD 0
theorem radialSum_5_checked : radialSum_5.Check nodes 10 := by decide
def radialSum_6 : SumRecipe where
  term := fun i => #[435,473,534,591,650,707,11,1107,1458,1906][i]?.getD 0
  accumulator := fun i => #[11,435,474,535,592,651,708,708,1109,1460,1908][i]?.getD 0
theorem radialSum_6_checked : radialSum_6.Check nodes 10 := by decide
def radialSum_7 : SumRecipe where
  term := fun i => #[756,811,870,927,986,1043,1107,11,1518,1965][i]?.getD 0
  accumulator := fun i => #[11,756,812,871,928,987,1044,1108,1108,1520,1967][i]?.getD 0
theorem radialSum_7_checked : radialSum_7.Check nodes 10 := by decide
def radialSum_8 : SumRecipe where
  term := fun i => #[1144,1184,1241,1298,1355,1412,1458,1518,11,2022][i]?.getD 0
  accumulator := fun i => #[11,1144,1185,1242,1299,1356,1413,1459,1519,1519,2024][i]?.getD 0
theorem radialSum_8_checked : radialSum_8.Check nodes 10 := by decide
def radialSum_9 : SumRecipe where
  term := fun i => #[1566,1621,1678,1735,1792,1849,1906,1965,2022,11][i]?.getD 0
  accumulator := fun i => #[11,1566,1622,1679,1736,1793,1850,1907,1966,2023,2023][i]?.getD 0
theorem radialSum_9_checked : radialSum_9.Check nodes 10 := by decide
def radialSums : Fin 10 → SumRecipe := ![radialSum_0,radialSum_1,radialSum_2,radialSum_3,radialSum_4,radialSum_5,radialSum_6,radialSum_7,radialSum_8,radialSum_9]
theorem radial_sums_checked (i : Fin 10) : (radialSums i).Check nodes 10 := by
  fin_cases i
  · exact radialSum_0_checked
  · exact radialSum_1_checked
  · exact radialSum_2_checked
  · exact radialSum_3_checked
  · exact radialSum_4_checked
  · exact radialSum_5_checked
  · exact radialSum_6_checked
  · exact radialSum_7_checked
  · exact radialSum_8_checked
  · exact radialSum_9_checked
theorem radial_sum_term (i j : Fin 10) : (radialSums i).term j =
    if i = j then 11 else (halfInverseRecipes (pairIndex i j)).negative := by
  revert i j; decide
theorem radial_sum_output (i : Fin 10) : (radialSums i).accumulator 10 = lambdaIndices i := by
  revert i; decide
theorem radial_entry_sound (r : ℝ) (i : Fin 10) :
    value (parameterInputs r) nodes (lambdaIndices i) = radialCoefficient (candidateAt r) i := by
  rw [← radial_sum_output, SumRecipe.sound_fin _ _ _ _ (radial_sums_checked i)]
  calc
    _ = ∑ j : Fin 10, -(‖candidateAt r i-candidateAt r j‖⁻¹/2) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [radial_sum_term]
      by_cases hij : i = j
      · subst j; simp [literal_zero]
      · rw [if_neg hij, unordered_half_inverse_sound r i j hij]
    _ = _ := by rw [Finset.sum_neg_distrib, ← Finset.sum_div]; simp [radialCoefficient, neg_div]
theorem lagrange_correction_checked (i : Fin 10) :
    ExtendedSmartMulCheck nodes (lambdaIndices i) 15 (lagrangeCorrections i) := by
  revert i; decide
theorem constrained_checked (ia jb : Fin 10 × Fin 3) :
    ExtendedSmartAddCheck nodes (laplacianIndices (flatIndex ia) (flatIndex jb))
      (if ia = jb then lagrangeCorrections ia.1 else 11)
      (constrainedIndices (flatIndex ia) (flatIndex jb)) := by
  revert ia jb; decide
theorem constrained_entry_sound (r : ℝ) (ia jb : Fin 10 × Fin 3) :
    value (parameterInputs r) nodes (constrainedIndices (flatIndex ia) (flatIndex jb)) =
      constrainedHessian (candidateAt r) ia jb := by
  rw [extendedSmartAdd_sound _ _ _ _ _ (constrained_checked ia jb), laplacian_entry_sound]
  by_cases hij : ia = jb
  · subst jb
    rw [if_pos rfl, extendedSmartMul_sound _ _ _ _ _ (lagrange_correction_checked ia.1),
      radial_entry_sound, literal_minus_one]
    simp [constrainedHessian, Matrix.sub_apply, Matrix.diagonal_apply, sub_eq_add_neg]
  · rw [if_neg hij, literal_zero]
    simp [constrainedHessian, Matrix.sub_apply, Matrix.diagonal_apply, hij]
def rotationIndices : Fin 10 → Fin 3 → Fin 3 → ℕ := ![![![11,2,11],![15,11,11],![11,11,11]],![![11,15,11],![2,11,11],![11,11,11]],![![11,0,11],![12,11,5],![11,13,11]],![![11,0,13],![12,11,11],![5,11,11]],![![11,0,11],![12,11,13],![11,345,11]],![![11,0,345],![12,11,11],![13,11,11]],![![11,12,14],![1048,11,10],![10,14,11]],![![11,12,14],![1048,11,14],![10,1461,11]],![![11,12,1461],![1048,11,14],![14,1461,11]],![![11,12,1461],![1048,11,10],![14,14,11]]]
theorem rotations_checked : RotationCheck nodes pointIndices rotationIndices := by decide
theorem rotation_entry_sound (r : ℝ) (ia : Fin 10 × Fin 3) (k : Fin 3) :
    value (parameterInputs r) nodes (rotationIndices ia.1 ia.2 k) =
      rotationColumns (candidateAt r) ia k :=
  rotation_recipe_sound _ nodes pointIndices rotationIndices rotations_checked _
    (coordinate_recipe_sound r nodes coordinate_prefix_checked) ia.1 ia.2 k
def rotationDot_0_0 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,2,11][i]?.getD 0
  accumulator := fun i => #[11,11,2,2][i]?.getD 0
theorem rotationDot_0_0_checked : rotationDot_0_0.ExtendedCheck nodes 3 := by decide
def rotationDot_0_1 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_1_checked : rotationDot_0_1.ExtendedCheck nodes 3 := by decide
def rotationDot_0_2 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_2_checked : rotationDot_0_2.ExtendedCheck nodes 3 := by decide
def rotationDot_0_3 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,15,11][i]?.getD 0
  accumulator := fun i => #[11,11,15,15][i]?.getD 0
theorem rotationDot_0_3_checked : rotationDot_0_3.ExtendedCheck nodes 3 := by decide
def rotationDot_0_4 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_4_checked : rotationDot_0_4.ExtendedCheck nodes 3 := by decide
def rotationDot_0_5 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_5_checked : rotationDot_0_5.ExtendedCheck nodes 3 := by decide
def rotationDot_0_6 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_0_6_checked : rotationDot_0_6.ExtendedCheck nodes 3 := by decide
def rotationDot_0_7 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_7_checked : rotationDot_0_7.ExtendedCheck nodes 3 := by decide
def rotationDot_0_8 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,13,11][i]?.getD 0
  accumulator := fun i => #[11,11,13,13][i]?.getD 0
theorem rotationDot_0_8_checked : rotationDot_0_8.ExtendedCheck nodes 3 := by decide
def rotationDot_0_9 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_0_9_checked : rotationDot_0_9.ExtendedCheck nodes 3 := by decide
def rotationDot_0_10 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_10_checked : rotationDot_0_10.ExtendedCheck nodes 3 := by decide
def rotationDot_0_11 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_11_checked : rotationDot_0_11.ExtendedCheck nodes 3 := by decide
def rotationDot_0_12 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_0_12_checked : rotationDot_0_12.ExtendedCheck nodes 3 := by decide
def rotationDot_0_13 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_13_checked : rotationDot_0_13.ExtendedCheck nodes 3 := by decide
def rotationDot_0_14 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,345,11][i]?.getD 0
  accumulator := fun i => #[11,11,345,345][i]?.getD 0
theorem rotationDot_0_14_checked : rotationDot_0_14.ExtendedCheck nodes 3 := by decide
def rotationDot_0_15 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_0_15_checked : rotationDot_0_15.ExtendedCheck nodes 3 := by decide
def rotationDot_0_16 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_16_checked : rotationDot_0_16.ExtendedCheck nodes 3 := by decide
def rotationDot_0_17 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_17_checked : rotationDot_0_17.ExtendedCheck nodes 3 := by decide
def rotationDot_0_18 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_0_18_checked : rotationDot_0_18.ExtendedCheck nodes 3 := by decide
def rotationDot_0_19 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_19_checked : rotationDot_0_19.ExtendedCheck nodes 3 := by decide
def rotationDot_0_20 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,14,11][i]?.getD 0
  accumulator := fun i => #[11,11,14,14][i]?.getD 0
theorem rotationDot_0_20_checked : rotationDot_0_20.ExtendedCheck nodes 3 := by decide
def rotationDot_0_21 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_0_21_checked : rotationDot_0_21.ExtendedCheck nodes 3 := by decide
def rotationDot_0_22 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_22_checked : rotationDot_0_22.ExtendedCheck nodes 3 := by decide
def rotationDot_0_23 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,1461,11][i]?.getD 0
  accumulator := fun i => #[11,11,1461,1461][i]?.getD 0
theorem rotationDot_0_23_checked : rotationDot_0_23.ExtendedCheck nodes 3 := by decide
def rotationDot_0_24 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_0_24_checked : rotationDot_0_24.ExtendedCheck nodes 3 := by decide
def rotationDot_0_25 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_25_checked : rotationDot_0_25.ExtendedCheck nodes 3 := by decide
def rotationDot_0_26 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,1461,11][i]?.getD 0
  accumulator := fun i => #[11,11,1461,1461][i]?.getD 0
theorem rotationDot_0_26_checked : rotationDot_0_26.ExtendedCheck nodes 3 := by decide
def rotationDot_0_27 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_0_27_checked : rotationDot_0_27.ExtendedCheck nodes 3 := by decide
def rotationDot_0_28 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_0_28_checked : rotationDot_0_28.ExtendedCheck nodes 3 := by decide
def rotationDot_0_29 : DotRecipe where
  left := fun i => #[11,2,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,14,11][i]?.getD 0
  accumulator := fun i => #[11,11,14,14][i]?.getD 0
theorem rotationDot_0_29_checked : rotationDot_0_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow0 : Array DotRecipe := #[rotationDot_0_0,rotationDot_0_1,rotationDot_0_2,rotationDot_0_3,rotationDot_0_4,rotationDot_0_5,rotationDot_0_6,rotationDot_0_7,rotationDot_0_8,rotationDot_0_9,rotationDot_0_10,rotationDot_0_11,rotationDot_0_12,rotationDot_0_13,rotationDot_0_14,rotationDot_0_15,rotationDot_0_16,rotationDot_0_17,rotationDot_0_18,rotationDot_0_19,rotationDot_0_20,rotationDot_0_21,rotationDot_0_22,rotationDot_0_23,rotationDot_0_24,rotationDot_0_25,rotationDot_0_26,rotationDot_0_27,rotationDot_0_28,rotationDot_0_29]
theorem rotationDotsRow0_checked (j : Fin 30) :
    (rotationDotsRow0[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_0_0_checked
  · exact rotationDot_0_1_checked
  · exact rotationDot_0_2_checked
  · exact rotationDot_0_3_checked
  · exact rotationDot_0_4_checked
  · exact rotationDot_0_5_checked
  · exact rotationDot_0_6_checked
  · exact rotationDot_0_7_checked
  · exact rotationDot_0_8_checked
  · exact rotationDot_0_9_checked
  · exact rotationDot_0_10_checked
  · exact rotationDot_0_11_checked
  · exact rotationDot_0_12_checked
  · exact rotationDot_0_13_checked
  · exact rotationDot_0_14_checked
  · exact rotationDot_0_15_checked
  · exact rotationDot_0_16_checked
  · exact rotationDot_0_17_checked
  · exact rotationDot_0_18_checked
  · exact rotationDot_0_19_checked
  · exact rotationDot_0_20_checked
  · exact rotationDot_0_21_checked
  · exact rotationDot_0_22_checked
  · exact rotationDot_0_23_checked
  · exact rotationDot_0_24_checked
  · exact rotationDot_0_25_checked
  · exact rotationDot_0_26_checked
  · exact rotationDot_0_27_checked
  · exact rotationDot_0_28_checked
  · exact rotationDot_0_29_checked
def rotationDot_1_0 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_0_checked : rotationDot_1_0.ExtendedCheck nodes 3 := by decide
def rotationDot_1_1 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2,11,11][i]?.getD 0
  accumulator := fun i => #[11,2,2,2][i]?.getD 0
theorem rotationDot_1_1_checked : rotationDot_1_1.ExtendedCheck nodes 3 := by decide
def rotationDot_1_2 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_2_checked : rotationDot_1_2.ExtendedCheck nodes 3 := by decide
def rotationDot_1_3 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_3_checked : rotationDot_1_3.ExtendedCheck nodes 3 := by decide
def rotationDot_1_4 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[15,11,11][i]?.getD 0
  accumulator := fun i => #[11,15,15,15][i]?.getD 0
theorem rotationDot_1_4_checked : rotationDot_1_4.ExtendedCheck nodes 3 := by decide
def rotationDot_1_5 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_5_checked : rotationDot_1_5.ExtendedCheck nodes 3 := by decide
def rotationDot_1_6 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_6_checked : rotationDot_1_6.ExtendedCheck nodes 3 := by decide
def rotationDot_1_7 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2082,11,11][i]?.getD 0
  accumulator := fun i => #[11,2082,2082,2082][i]?.getD 0
theorem rotationDot_1_7_checked : rotationDot_1_7.ExtendedCheck nodes 3 := by decide
def rotationDot_1_8 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_8_checked : rotationDot_1_8.ExtendedCheck nodes 3 := by decide
def rotationDot_1_9 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_9_checked : rotationDot_1_9.ExtendedCheck nodes 3 := by decide
def rotationDot_1_10 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2082,11,11][i]?.getD 0
  accumulator := fun i => #[11,2082,2082,2082][i]?.getD 0
theorem rotationDot_1_10_checked : rotationDot_1_10.ExtendedCheck nodes 3 := by decide
def rotationDot_1_11 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2085,11,11][i]?.getD 0
  accumulator := fun i => #[11,2085,2085,2085][i]?.getD 0
theorem rotationDot_1_11_checked : rotationDot_1_11.ExtendedCheck nodes 3 := by decide
def rotationDot_1_12 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_12_checked : rotationDot_1_12.ExtendedCheck nodes 3 := by decide
def rotationDot_1_13 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2082,11,11][i]?.getD 0
  accumulator := fun i => #[11,2082,2082,2082][i]?.getD 0
theorem rotationDot_1_13_checked : rotationDot_1_13.ExtendedCheck nodes 3 := by decide
def rotationDot_1_14 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_14_checked : rotationDot_1_14.ExtendedCheck nodes 3 := by decide
def rotationDot_1_15 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_15_checked : rotationDot_1_15.ExtendedCheck nodes 3 := by decide
def rotationDot_1_16 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2082,11,11][i]?.getD 0
  accumulator := fun i => #[11,2082,2082,2082][i]?.getD 0
theorem rotationDot_1_16_checked : rotationDot_1_16.ExtendedCheck nodes 3 := by decide
def rotationDot_1_17 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2089,11,11][i]?.getD 0
  accumulator := fun i => #[11,2089,2089,2089][i]?.getD 0
theorem rotationDot_1_17_checked : rotationDot_1_17.ExtendedCheck nodes 3 := by decide
def rotationDot_1_18 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_18_checked : rotationDot_1_18.ExtendedCheck nodes 3 := by decide
def rotationDot_1_19 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2091,11,11][i]?.getD 0
  accumulator := fun i => #[11,2091,2091,2091][i]?.getD 0
theorem rotationDot_1_19_checked : rotationDot_1_19.ExtendedCheck nodes 3 := by decide
def rotationDot_1_20 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2093,11,11][i]?.getD 0
  accumulator := fun i => #[11,2093,2093,2093][i]?.getD 0
theorem rotationDot_1_20_checked : rotationDot_1_20.ExtendedCheck nodes 3 := by decide
def rotationDot_1_21 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_21_checked : rotationDot_1_21.ExtendedCheck nodes 3 := by decide
def rotationDot_1_22 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2091,11,11][i]?.getD 0
  accumulator := fun i => #[11,2091,2091,2091][i]?.getD 0
theorem rotationDot_1_22_checked : rotationDot_1_22.ExtendedCheck nodes 3 := by decide
def rotationDot_1_23 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2093,11,11][i]?.getD 0
  accumulator := fun i => #[11,2093,2093,2093][i]?.getD 0
theorem rotationDot_1_23_checked : rotationDot_1_23.ExtendedCheck nodes 3 := by decide
def rotationDot_1_24 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_24_checked : rotationDot_1_24.ExtendedCheck nodes 3 := by decide
def rotationDot_1_25 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2091,11,11][i]?.getD 0
  accumulator := fun i => #[11,2091,2091,2091][i]?.getD 0
theorem rotationDot_1_25_checked : rotationDot_1_25.ExtendedCheck nodes 3 := by decide
def rotationDot_1_26 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2098,11,11][i]?.getD 0
  accumulator := fun i => #[11,2098,2098,2098][i]?.getD 0
theorem rotationDot_1_26_checked : rotationDot_1_26.ExtendedCheck nodes 3 := by decide
def rotationDot_1_27 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_1_27_checked : rotationDot_1_27.ExtendedCheck nodes 3 := by decide
def rotationDot_1_28 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2091,11,11][i]?.getD 0
  accumulator := fun i => #[11,2091,2091,2091][i]?.getD 0
theorem rotationDot_1_28_checked : rotationDot_1_28.ExtendedCheck nodes 3 := by decide
def rotationDot_1_29 : DotRecipe where
  left := fun i => #[15,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2098,11,11][i]?.getD 0
  accumulator := fun i => #[11,2098,2098,2098][i]?.getD 0
theorem rotationDot_1_29_checked : rotationDot_1_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow1 : Array DotRecipe := #[rotationDot_1_0,rotationDot_1_1,rotationDot_1_2,rotationDot_1_3,rotationDot_1_4,rotationDot_1_5,rotationDot_1_6,rotationDot_1_7,rotationDot_1_8,rotationDot_1_9,rotationDot_1_10,rotationDot_1_11,rotationDot_1_12,rotationDot_1_13,rotationDot_1_14,rotationDot_1_15,rotationDot_1_16,rotationDot_1_17,rotationDot_1_18,rotationDot_1_19,rotationDot_1_20,rotationDot_1_21,rotationDot_1_22,rotationDot_1_23,rotationDot_1_24,rotationDot_1_25,rotationDot_1_26,rotationDot_1_27,rotationDot_1_28,rotationDot_1_29]
theorem rotationDotsRow1_checked (j : Fin 30) :
    (rotationDotsRow1[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_1_0_checked
  · exact rotationDot_1_1_checked
  · exact rotationDot_1_2_checked
  · exact rotationDot_1_3_checked
  · exact rotationDot_1_4_checked
  · exact rotationDot_1_5_checked
  · exact rotationDot_1_6_checked
  · exact rotationDot_1_7_checked
  · exact rotationDot_1_8_checked
  · exact rotationDot_1_9_checked
  · exact rotationDot_1_10_checked
  · exact rotationDot_1_11_checked
  · exact rotationDot_1_12_checked
  · exact rotationDot_1_13_checked
  · exact rotationDot_1_14_checked
  · exact rotationDot_1_15_checked
  · exact rotationDot_1_16_checked
  · exact rotationDot_1_17_checked
  · exact rotationDot_1_18_checked
  · exact rotationDot_1_19_checked
  · exact rotationDot_1_20_checked
  · exact rotationDot_1_21_checked
  · exact rotationDot_1_22_checked
  · exact rotationDot_1_23_checked
  · exact rotationDot_1_24_checked
  · exact rotationDot_1_25_checked
  · exact rotationDot_1_26_checked
  · exact rotationDot_1_27_checked
  · exact rotationDot_1_28_checked
  · exact rotationDot_1_29_checked
def rotationDot_2_0 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_0_checked : rotationDot_2_0.ExtendedCheck nodes 3 := by decide
def rotationDot_2_1 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_1_checked : rotationDot_2_1.ExtendedCheck nodes 3 := by decide
def rotationDot_2_2 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_2_checked : rotationDot_2_2.ExtendedCheck nodes 3 := by decide
def rotationDot_2_3 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_3_checked : rotationDot_2_3.ExtendedCheck nodes 3 := by decide
def rotationDot_2_4 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_4_checked : rotationDot_2_4.ExtendedCheck nodes 3 := by decide
def rotationDot_2_5 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_5_checked : rotationDot_2_5.ExtendedCheck nodes 3 := by decide
def rotationDot_2_6 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_6_checked : rotationDot_2_6.ExtendedCheck nodes 3 := by decide
def rotationDot_2_7 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_7_checked : rotationDot_2_7.ExtendedCheck nodes 3 := by decide
def rotationDot_2_8 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_8_checked : rotationDot_2_8.ExtendedCheck nodes 3 := by decide
def rotationDot_2_9 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_9_checked : rotationDot_2_9.ExtendedCheck nodes 3 := by decide
def rotationDot_2_10 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_10_checked : rotationDot_2_10.ExtendedCheck nodes 3 := by decide
def rotationDot_2_11 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_11_checked : rotationDot_2_11.ExtendedCheck nodes 3 := by decide
def rotationDot_2_12 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_12_checked : rotationDot_2_12.ExtendedCheck nodes 3 := by decide
def rotationDot_2_13 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_13_checked : rotationDot_2_13.ExtendedCheck nodes 3 := by decide
def rotationDot_2_14 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_14_checked : rotationDot_2_14.ExtendedCheck nodes 3 := by decide
def rotationDot_2_15 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_15_checked : rotationDot_2_15.ExtendedCheck nodes 3 := by decide
def rotationDot_2_16 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_16_checked : rotationDot_2_16.ExtendedCheck nodes 3 := by decide
def rotationDot_2_17 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_17_checked : rotationDot_2_17.ExtendedCheck nodes 3 := by decide
def rotationDot_2_18 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_18_checked : rotationDot_2_18.ExtendedCheck nodes 3 := by decide
def rotationDot_2_19 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_19_checked : rotationDot_2_19.ExtendedCheck nodes 3 := by decide
def rotationDot_2_20 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_20_checked : rotationDot_2_20.ExtendedCheck nodes 3 := by decide
def rotationDot_2_21 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_21_checked : rotationDot_2_21.ExtendedCheck nodes 3 := by decide
def rotationDot_2_22 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_22_checked : rotationDot_2_22.ExtendedCheck nodes 3 := by decide
def rotationDot_2_23 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_23_checked : rotationDot_2_23.ExtendedCheck nodes 3 := by decide
def rotationDot_2_24 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_24_checked : rotationDot_2_24.ExtendedCheck nodes 3 := by decide
def rotationDot_2_25 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_25_checked : rotationDot_2_25.ExtendedCheck nodes 3 := by decide
def rotationDot_2_26 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_26_checked : rotationDot_2_26.ExtendedCheck nodes 3 := by decide
def rotationDot_2_27 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_27_checked : rotationDot_2_27.ExtendedCheck nodes 3 := by decide
def rotationDot_2_28 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_28_checked : rotationDot_2_28.ExtendedCheck nodes 3 := by decide
def rotationDot_2_29 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_2_29_checked : rotationDot_2_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow2 : Array DotRecipe := #[rotationDot_2_0,rotationDot_2_1,rotationDot_2_2,rotationDot_2_3,rotationDot_2_4,rotationDot_2_5,rotationDot_2_6,rotationDot_2_7,rotationDot_2_8,rotationDot_2_9,rotationDot_2_10,rotationDot_2_11,rotationDot_2_12,rotationDot_2_13,rotationDot_2_14,rotationDot_2_15,rotationDot_2_16,rotationDot_2_17,rotationDot_2_18,rotationDot_2_19,rotationDot_2_20,rotationDot_2_21,rotationDot_2_22,rotationDot_2_23,rotationDot_2_24,rotationDot_2_25,rotationDot_2_26,rotationDot_2_27,rotationDot_2_28,rotationDot_2_29]
theorem rotationDotsRow2_checked (j : Fin 30) :
    (rotationDotsRow2[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_2_0_checked
  · exact rotationDot_2_1_checked
  · exact rotationDot_2_2_checked
  · exact rotationDot_2_3_checked
  · exact rotationDot_2_4_checked
  · exact rotationDot_2_5_checked
  · exact rotationDot_2_6_checked
  · exact rotationDot_2_7_checked
  · exact rotationDot_2_8_checked
  · exact rotationDot_2_9_checked
  · exact rotationDot_2_10_checked
  · exact rotationDot_2_11_checked
  · exact rotationDot_2_12_checked
  · exact rotationDot_2_13_checked
  · exact rotationDot_2_14_checked
  · exact rotationDot_2_15_checked
  · exact rotationDot_2_16_checked
  · exact rotationDot_2_17_checked
  · exact rotationDot_2_18_checked
  · exact rotationDot_2_19_checked
  · exact rotationDot_2_20_checked
  · exact rotationDot_2_21_checked
  · exact rotationDot_2_22_checked
  · exact rotationDot_2_23_checked
  · exact rotationDot_2_24_checked
  · exact rotationDot_2_25_checked
  · exact rotationDot_2_26_checked
  · exact rotationDot_2_27_checked
  · exact rotationDot_2_28_checked
  · exact rotationDot_2_29_checked
def rotationDot_3_0 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,15,11][i]?.getD 0
  accumulator := fun i => #[11,11,15,15][i]?.getD 0
theorem rotationDot_3_0_checked : rotationDot_3_0.ExtendedCheck nodes 3 := by decide
def rotationDot_3_1 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_1_checked : rotationDot_3_1.ExtendedCheck nodes 3 := by decide
def rotationDot_3_2 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_2_checked : rotationDot_3_2.ExtendedCheck nodes 3 := by decide
def rotationDot_3_3 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2,11][i]?.getD 0
  accumulator := fun i => #[11,11,2,2][i]?.getD 0
theorem rotationDot_3_3_checked : rotationDot_3_3.ExtendedCheck nodes 3 := by decide
def rotationDot_3_4 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_4_checked : rotationDot_3_4.ExtendedCheck nodes 3 := by decide
def rotationDot_3_5 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_5_checked : rotationDot_3_5.ExtendedCheck nodes 3 := by decide
def rotationDot_3_6 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2103,11][i]?.getD 0
  accumulator := fun i => #[11,11,2103,2103][i]?.getD 0
theorem rotationDot_3_6_checked : rotationDot_3_6.ExtendedCheck nodes 3 := by decide
def rotationDot_3_7 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_7_checked : rotationDot_3_7.ExtendedCheck nodes 3 := by decide
def rotationDot_3_8 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2089,11][i]?.getD 0
  accumulator := fun i => #[11,11,2089,2089][i]?.getD 0
theorem rotationDot_3_8_checked : rotationDot_3_8.ExtendedCheck nodes 3 := by decide
def rotationDot_3_9 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2103,11][i]?.getD 0
  accumulator := fun i => #[11,11,2103,2103][i]?.getD 0
theorem rotationDot_3_9_checked : rotationDot_3_9.ExtendedCheck nodes 3 := by decide
def rotationDot_3_10 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_10_checked : rotationDot_3_10.ExtendedCheck nodes 3 := by decide
def rotationDot_3_11 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_11_checked : rotationDot_3_11.ExtendedCheck nodes 3 := by decide
def rotationDot_3_12 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2103,11][i]?.getD 0
  accumulator := fun i => #[11,11,2103,2103][i]?.getD 0
theorem rotationDot_3_12_checked : rotationDot_3_12.ExtendedCheck nodes 3 := by decide
def rotationDot_3_13 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_13_checked : rotationDot_3_13.ExtendedCheck nodes 3 := by decide
def rotationDot_3_14 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2108,11][i]?.getD 0
  accumulator := fun i => #[11,11,2108,2108][i]?.getD 0
theorem rotationDot_3_14_checked : rotationDot_3_14.ExtendedCheck nodes 3 := by decide
def rotationDot_3_15 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2103,11][i]?.getD 0
  accumulator := fun i => #[11,11,2103,2103][i]?.getD 0
theorem rotationDot_3_15_checked : rotationDot_3_15.ExtendedCheck nodes 3 := by decide
def rotationDot_3_16 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_16_checked : rotationDot_3_16.ExtendedCheck nodes 3 := by decide
def rotationDot_3_17 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_17_checked : rotationDot_3_17.ExtendedCheck nodes 3 := by decide
def rotationDot_3_18 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2082,11][i]?.getD 0
  accumulator := fun i => #[11,11,2082,2082][i]?.getD 0
theorem rotationDot_3_18_checked : rotationDot_3_18.ExtendedCheck nodes 3 := by decide
def rotationDot_3_19 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_19_checked : rotationDot_3_19.ExtendedCheck nodes 3 := by decide
def rotationDot_3_20 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2098,11][i]?.getD 0
  accumulator := fun i => #[11,11,2098,2098][i]?.getD 0
theorem rotationDot_3_20_checked : rotationDot_3_20.ExtendedCheck nodes 3 := by decide
def rotationDot_3_21 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2082,11][i]?.getD 0
  accumulator := fun i => #[11,11,2082,2082][i]?.getD 0
theorem rotationDot_3_21_checked : rotationDot_3_21.ExtendedCheck nodes 3 := by decide
def rotationDot_3_22 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_22_checked : rotationDot_3_22.ExtendedCheck nodes 3 := by decide
def rotationDot_3_23 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2114,11][i]?.getD 0
  accumulator := fun i => #[11,11,2114,2114][i]?.getD 0
theorem rotationDot_3_23_checked : rotationDot_3_23.ExtendedCheck nodes 3 := by decide
def rotationDot_3_24 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2082,11][i]?.getD 0
  accumulator := fun i => #[11,11,2082,2082][i]?.getD 0
theorem rotationDot_3_24_checked : rotationDot_3_24.ExtendedCheck nodes 3 := by decide
def rotationDot_3_25 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_25_checked : rotationDot_3_25.ExtendedCheck nodes 3 := by decide
def rotationDot_3_26 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2114,11][i]?.getD 0
  accumulator := fun i => #[11,11,2114,2114][i]?.getD 0
theorem rotationDot_3_26_checked : rotationDot_3_26.ExtendedCheck nodes 3 := by decide
def rotationDot_3_27 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2082,11][i]?.getD 0
  accumulator := fun i => #[11,11,2082,2082][i]?.getD 0
theorem rotationDot_3_27_checked : rotationDot_3_27.ExtendedCheck nodes 3 := by decide
def rotationDot_3_28 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_3_28_checked : rotationDot_3_28.ExtendedCheck nodes 3 := by decide
def rotationDot_3_29 : DotRecipe where
  left := fun i => #[11,15,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2098,11][i]?.getD 0
  accumulator := fun i => #[11,11,2098,2098][i]?.getD 0
theorem rotationDot_3_29_checked : rotationDot_3_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow3 : Array DotRecipe := #[rotationDot_3_0,rotationDot_3_1,rotationDot_3_2,rotationDot_3_3,rotationDot_3_4,rotationDot_3_5,rotationDot_3_6,rotationDot_3_7,rotationDot_3_8,rotationDot_3_9,rotationDot_3_10,rotationDot_3_11,rotationDot_3_12,rotationDot_3_13,rotationDot_3_14,rotationDot_3_15,rotationDot_3_16,rotationDot_3_17,rotationDot_3_18,rotationDot_3_19,rotationDot_3_20,rotationDot_3_21,rotationDot_3_22,rotationDot_3_23,rotationDot_3_24,rotationDot_3_25,rotationDot_3_26,rotationDot_3_27,rotationDot_3_28,rotationDot_3_29]
theorem rotationDotsRow3_checked (j : Fin 30) :
    (rotationDotsRow3[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_3_0_checked
  · exact rotationDot_3_1_checked
  · exact rotationDot_3_2_checked
  · exact rotationDot_3_3_checked
  · exact rotationDot_3_4_checked
  · exact rotationDot_3_5_checked
  · exact rotationDot_3_6_checked
  · exact rotationDot_3_7_checked
  · exact rotationDot_3_8_checked
  · exact rotationDot_3_9_checked
  · exact rotationDot_3_10_checked
  · exact rotationDot_3_11_checked
  · exact rotationDot_3_12_checked
  · exact rotationDot_3_13_checked
  · exact rotationDot_3_14_checked
  · exact rotationDot_3_15_checked
  · exact rotationDot_3_16_checked
  · exact rotationDot_3_17_checked
  · exact rotationDot_3_18_checked
  · exact rotationDot_3_19_checked
  · exact rotationDot_3_20_checked
  · exact rotationDot_3_21_checked
  · exact rotationDot_3_22_checked
  · exact rotationDot_3_23_checked
  · exact rotationDot_3_24_checked
  · exact rotationDot_3_25_checked
  · exact rotationDot_3_26_checked
  · exact rotationDot_3_27_checked
  · exact rotationDot_3_28_checked
  · exact rotationDot_3_29_checked
def rotationDot_4_0 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_0_checked : rotationDot_4_0.ExtendedCheck nodes 3 := by decide
def rotationDot_4_1 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[15,11,11][i]?.getD 0
  accumulator := fun i => #[11,15,15,15][i]?.getD 0
theorem rotationDot_4_1_checked : rotationDot_4_1.ExtendedCheck nodes 3 := by decide
def rotationDot_4_2 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_2_checked : rotationDot_4_2.ExtendedCheck nodes 3 := by decide
def rotationDot_4_3 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_3_checked : rotationDot_4_3.ExtendedCheck nodes 3 := by decide
def rotationDot_4_4 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[2,11,11][i]?.getD 0
  accumulator := fun i => #[11,2,2,2][i]?.getD 0
theorem rotationDot_4_4_checked : rotationDot_4_4.ExtendedCheck nodes 3 := by decide
def rotationDot_4_5 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_5_checked : rotationDot_4_5.ExtendedCheck nodes 3 := by decide
def rotationDot_4_6 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_6_checked : rotationDot_4_6.ExtendedCheck nodes 3 := by decide
def rotationDot_4_7 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_4_7_checked : rotationDot_4_7.ExtendedCheck nodes 3 := by decide
def rotationDot_4_8 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_8_checked : rotationDot_4_8.ExtendedCheck nodes 3 := by decide
def rotationDot_4_9 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_9_checked : rotationDot_4_9.ExtendedCheck nodes 3 := by decide
def rotationDot_4_10 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_4_10_checked : rotationDot_4_10.ExtendedCheck nodes 3 := by decide
def rotationDot_4_11 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[5,11,11][i]?.getD 0
  accumulator := fun i => #[11,5,5,5][i]?.getD 0
theorem rotationDot_4_11_checked : rotationDot_4_11.ExtendedCheck nodes 3 := by decide
def rotationDot_4_12 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_12_checked : rotationDot_4_12.ExtendedCheck nodes 3 := by decide
def rotationDot_4_13 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_4_13_checked : rotationDot_4_13.ExtendedCheck nodes 3 := by decide
def rotationDot_4_14 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_14_checked : rotationDot_4_14.ExtendedCheck nodes 3 := by decide
def rotationDot_4_15 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_15_checked : rotationDot_4_15.ExtendedCheck nodes 3 := by decide
def rotationDot_4_16 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_4_16_checked : rotationDot_4_16.ExtendedCheck nodes 3 := by decide
def rotationDot_4_17 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[13,11,11][i]?.getD 0
  accumulator := fun i => #[11,13,13,13][i]?.getD 0
theorem rotationDot_4_17_checked : rotationDot_4_17.ExtendedCheck nodes 3 := by decide
def rotationDot_4_18 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_18_checked : rotationDot_4_18.ExtendedCheck nodes 3 := by decide
def rotationDot_4_19 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_4_19_checked : rotationDot_4_19.ExtendedCheck nodes 3 := by decide
def rotationDot_4_20 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[10,11,11][i]?.getD 0
  accumulator := fun i => #[11,10,10,10][i]?.getD 0
theorem rotationDot_4_20_checked : rotationDot_4_20.ExtendedCheck nodes 3 := by decide
def rotationDot_4_21 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_21_checked : rotationDot_4_21.ExtendedCheck nodes 3 := by decide
def rotationDot_4_22 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_4_22_checked : rotationDot_4_22.ExtendedCheck nodes 3 := by decide
def rotationDot_4_23 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[10,11,11][i]?.getD 0
  accumulator := fun i => #[11,10,10,10][i]?.getD 0
theorem rotationDot_4_23_checked : rotationDot_4_23.ExtendedCheck nodes 3 := by decide
def rotationDot_4_24 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_24_checked : rotationDot_4_24.ExtendedCheck nodes 3 := by decide
def rotationDot_4_25 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_4_25_checked : rotationDot_4_25.ExtendedCheck nodes 3 := by decide
def rotationDot_4_26 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[14,11,11][i]?.getD 0
  accumulator := fun i => #[11,14,14,14][i]?.getD 0
theorem rotationDot_4_26_checked : rotationDot_4_26.ExtendedCheck nodes 3 := by decide
def rotationDot_4_27 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_4_27_checked : rotationDot_4_27.ExtendedCheck nodes 3 := by decide
def rotationDot_4_28 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_4_28_checked : rotationDot_4_28.ExtendedCheck nodes 3 := by decide
def rotationDot_4_29 : DotRecipe where
  left := fun i => #[2,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[14,11,11][i]?.getD 0
  accumulator := fun i => #[11,14,14,14][i]?.getD 0
theorem rotationDot_4_29_checked : rotationDot_4_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow4 : Array DotRecipe := #[rotationDot_4_0,rotationDot_4_1,rotationDot_4_2,rotationDot_4_3,rotationDot_4_4,rotationDot_4_5,rotationDot_4_6,rotationDot_4_7,rotationDot_4_8,rotationDot_4_9,rotationDot_4_10,rotationDot_4_11,rotationDot_4_12,rotationDot_4_13,rotationDot_4_14,rotationDot_4_15,rotationDot_4_16,rotationDot_4_17,rotationDot_4_18,rotationDot_4_19,rotationDot_4_20,rotationDot_4_21,rotationDot_4_22,rotationDot_4_23,rotationDot_4_24,rotationDot_4_25,rotationDot_4_26,rotationDot_4_27,rotationDot_4_28,rotationDot_4_29]
theorem rotationDotsRow4_checked (j : Fin 30) :
    (rotationDotsRow4[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_4_0_checked
  · exact rotationDot_4_1_checked
  · exact rotationDot_4_2_checked
  · exact rotationDot_4_3_checked
  · exact rotationDot_4_4_checked
  · exact rotationDot_4_5_checked
  · exact rotationDot_4_6_checked
  · exact rotationDot_4_7_checked
  · exact rotationDot_4_8_checked
  · exact rotationDot_4_9_checked
  · exact rotationDot_4_10_checked
  · exact rotationDot_4_11_checked
  · exact rotationDot_4_12_checked
  · exact rotationDot_4_13_checked
  · exact rotationDot_4_14_checked
  · exact rotationDot_4_15_checked
  · exact rotationDot_4_16_checked
  · exact rotationDot_4_17_checked
  · exact rotationDot_4_18_checked
  · exact rotationDot_4_19_checked
  · exact rotationDot_4_20_checked
  · exact rotationDot_4_21_checked
  · exact rotationDot_4_22_checked
  · exact rotationDot_4_23_checked
  · exact rotationDot_4_24_checked
  · exact rotationDot_4_25_checked
  · exact rotationDot_4_26_checked
  · exact rotationDot_4_27_checked
  · exact rotationDot_4_28_checked
  · exact rotationDot_4_29_checked
def rotationDot_5_0 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_0_checked : rotationDot_5_0.ExtendedCheck nodes 3 := by decide
def rotationDot_5_1 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_1_checked : rotationDot_5_1.ExtendedCheck nodes 3 := by decide
def rotationDot_5_2 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_2_checked : rotationDot_5_2.ExtendedCheck nodes 3 := by decide
def rotationDot_5_3 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_3_checked : rotationDot_5_3.ExtendedCheck nodes 3 := by decide
def rotationDot_5_4 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_4_checked : rotationDot_5_4.ExtendedCheck nodes 3 := by decide
def rotationDot_5_5 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_5_checked : rotationDot_5_5.ExtendedCheck nodes 3 := by decide
def rotationDot_5_6 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_6_checked : rotationDot_5_6.ExtendedCheck nodes 3 := by decide
def rotationDot_5_7 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_7_checked : rotationDot_5_7.ExtendedCheck nodes 3 := by decide
def rotationDot_5_8 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_8_checked : rotationDot_5_8.ExtendedCheck nodes 3 := by decide
def rotationDot_5_9 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_9_checked : rotationDot_5_9.ExtendedCheck nodes 3 := by decide
def rotationDot_5_10 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_10_checked : rotationDot_5_10.ExtendedCheck nodes 3 := by decide
def rotationDot_5_11 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_11_checked : rotationDot_5_11.ExtendedCheck nodes 3 := by decide
def rotationDot_5_12 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_12_checked : rotationDot_5_12.ExtendedCheck nodes 3 := by decide
def rotationDot_5_13 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_13_checked : rotationDot_5_13.ExtendedCheck nodes 3 := by decide
def rotationDot_5_14 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_14_checked : rotationDot_5_14.ExtendedCheck nodes 3 := by decide
def rotationDot_5_15 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_15_checked : rotationDot_5_15.ExtendedCheck nodes 3 := by decide
def rotationDot_5_16 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_16_checked : rotationDot_5_16.ExtendedCheck nodes 3 := by decide
def rotationDot_5_17 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_17_checked : rotationDot_5_17.ExtendedCheck nodes 3 := by decide
def rotationDot_5_18 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_18_checked : rotationDot_5_18.ExtendedCheck nodes 3 := by decide
def rotationDot_5_19 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_19_checked : rotationDot_5_19.ExtendedCheck nodes 3 := by decide
def rotationDot_5_20 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_20_checked : rotationDot_5_20.ExtendedCheck nodes 3 := by decide
def rotationDot_5_21 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_21_checked : rotationDot_5_21.ExtendedCheck nodes 3 := by decide
def rotationDot_5_22 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_22_checked : rotationDot_5_22.ExtendedCheck nodes 3 := by decide
def rotationDot_5_23 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_23_checked : rotationDot_5_23.ExtendedCheck nodes 3 := by decide
def rotationDot_5_24 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_24_checked : rotationDot_5_24.ExtendedCheck nodes 3 := by decide
def rotationDot_5_25 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_25_checked : rotationDot_5_25.ExtendedCheck nodes 3 := by decide
def rotationDot_5_26 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_26_checked : rotationDot_5_26.ExtendedCheck nodes 3 := by decide
def rotationDot_5_27 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_27_checked : rotationDot_5_27.ExtendedCheck nodes 3 := by decide
def rotationDot_5_28 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_28_checked : rotationDot_5_28.ExtendedCheck nodes 3 := by decide
def rotationDot_5_29 : DotRecipe where
  left := fun i => #[11,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_5_29_checked : rotationDot_5_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow5 : Array DotRecipe := #[rotationDot_5_0,rotationDot_5_1,rotationDot_5_2,rotationDot_5_3,rotationDot_5_4,rotationDot_5_5,rotationDot_5_6,rotationDot_5_7,rotationDot_5_8,rotationDot_5_9,rotationDot_5_10,rotationDot_5_11,rotationDot_5_12,rotationDot_5_13,rotationDot_5_14,rotationDot_5_15,rotationDot_5_16,rotationDot_5_17,rotationDot_5_18,rotationDot_5_19,rotationDot_5_20,rotationDot_5_21,rotationDot_5_22,rotationDot_5_23,rotationDot_5_24,rotationDot_5_25,rotationDot_5_26,rotationDot_5_27,rotationDot_5_28,rotationDot_5_29]
theorem rotationDotsRow5_checked (j : Fin 30) :
    (rotationDotsRow5[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_5_0_checked
  · exact rotationDot_5_1_checked
  · exact rotationDot_5_2_checked
  · exact rotationDot_5_3_checked
  · exact rotationDot_5_4_checked
  · exact rotationDot_5_5_checked
  · exact rotationDot_5_6_checked
  · exact rotationDot_5_7_checked
  · exact rotationDot_5_8_checked
  · exact rotationDot_5_9_checked
  · exact rotationDot_5_10_checked
  · exact rotationDot_5_11_checked
  · exact rotationDot_5_12_checked
  · exact rotationDot_5_13_checked
  · exact rotationDot_5_14_checked
  · exact rotationDot_5_15_checked
  · exact rotationDot_5_16_checked
  · exact rotationDot_5_17_checked
  · exact rotationDot_5_18_checked
  · exact rotationDot_5_19_checked
  · exact rotationDot_5_20_checked
  · exact rotationDot_5_21_checked
  · exact rotationDot_5_22_checked
  · exact rotationDot_5_23_checked
  · exact rotationDot_5_24_checked
  · exact rotationDot_5_25_checked
  · exact rotationDot_5_26_checked
  · exact rotationDot_5_27_checked
  · exact rotationDot_5_28_checked
  · exact rotationDot_5_29_checked
def rotationDot_6_0 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_6_0_checked : rotationDot_6_0.ExtendedCheck nodes 3 := by decide
def rotationDot_6_1 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_1_checked : rotationDot_6_1.ExtendedCheck nodes 3 := by decide
def rotationDot_6_2 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_2_checked : rotationDot_6_2.ExtendedCheck nodes 3 := by decide
def rotationDot_6_3 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2135,11][i]?.getD 0
  accumulator := fun i => #[11,11,2135,2135][i]?.getD 0
theorem rotationDot_6_3_checked : rotationDot_6_3.ExtendedCheck nodes 3 := by decide
def rotationDot_6_4 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_4_checked : rotationDot_6_4.ExtendedCheck nodes 3 := by decide
def rotationDot_6_5 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_5_checked : rotationDot_6_5.ExtendedCheck nodes 3 := by decide
def rotationDot_6_6 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_6_6_checked : rotationDot_6_6.ExtendedCheck nodes 3 := by decide
def rotationDot_6_7 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_7_checked : rotationDot_6_7.ExtendedCheck nodes 3 := by decide
def rotationDot_6_8 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2138,11][i]?.getD 0
  accumulator := fun i => #[11,11,2138,2138][i]?.getD 0
theorem rotationDot_6_8_checked : rotationDot_6_8.ExtendedCheck nodes 3 := by decide
def rotationDot_6_9 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_6_9_checked : rotationDot_6_9.ExtendedCheck nodes 3 := by decide
def rotationDot_6_10 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_10_checked : rotationDot_6_10.ExtendedCheck nodes 3 := by decide
def rotationDot_6_11 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_11_checked : rotationDot_6_11.ExtendedCheck nodes 3 := by decide
def rotationDot_6_12 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_6_12_checked : rotationDot_6_12.ExtendedCheck nodes 3 := by decide
def rotationDot_6_13 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_13_checked : rotationDot_6_13.ExtendedCheck nodes 3 := by decide
def rotationDot_6_14 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2142,11][i]?.getD 0
  accumulator := fun i => #[11,11,2142,2142][i]?.getD 0
theorem rotationDot_6_14_checked : rotationDot_6_14.ExtendedCheck nodes 3 := by decide
def rotationDot_6_15 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_6_15_checked : rotationDot_6_15.ExtendedCheck nodes 3 := by decide
def rotationDot_6_16 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_16_checked : rotationDot_6_16.ExtendedCheck nodes 3 := by decide
def rotationDot_6_17 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_17_checked : rotationDot_6_17.ExtendedCheck nodes 3 := by decide
def rotationDot_6_18 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_6_18_checked : rotationDot_6_18.ExtendedCheck nodes 3 := by decide
def rotationDot_6_19 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_19_checked : rotationDot_6_19.ExtendedCheck nodes 3 := by decide
def rotationDot_6_20 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_6_20_checked : rotationDot_6_20.ExtendedCheck nodes 3 := by decide
def rotationDot_6_21 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_6_21_checked : rotationDot_6_21.ExtendedCheck nodes 3 := by decide
def rotationDot_6_22 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_22_checked : rotationDot_6_22.ExtendedCheck nodes 3 := by decide
def rotationDot_6_23 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_6_23_checked : rotationDot_6_23.ExtendedCheck nodes 3 := by decide
def rotationDot_6_24 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_6_24_checked : rotationDot_6_24.ExtendedCheck nodes 3 := by decide
def rotationDot_6_25 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_25_checked : rotationDot_6_25.ExtendedCheck nodes 3 := by decide
def rotationDot_6_26 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_6_26_checked : rotationDot_6_26.ExtendedCheck nodes 3 := by decide
def rotationDot_6_27 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_6_27_checked : rotationDot_6_27.ExtendedCheck nodes 3 := by decide
def rotationDot_6_28 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_6_28_checked : rotationDot_6_28.ExtendedCheck nodes 3 := by decide
def rotationDot_6_29 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_6_29_checked : rotationDot_6_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow6 : Array DotRecipe := #[rotationDot_6_0,rotationDot_6_1,rotationDot_6_2,rotationDot_6_3,rotationDot_6_4,rotationDot_6_5,rotationDot_6_6,rotationDot_6_7,rotationDot_6_8,rotationDot_6_9,rotationDot_6_10,rotationDot_6_11,rotationDot_6_12,rotationDot_6_13,rotationDot_6_14,rotationDot_6_15,rotationDot_6_16,rotationDot_6_17,rotationDot_6_18,rotationDot_6_19,rotationDot_6_20,rotationDot_6_21,rotationDot_6_22,rotationDot_6_23,rotationDot_6_24,rotationDot_6_25,rotationDot_6_26,rotationDot_6_27,rotationDot_6_28,rotationDot_6_29]
theorem rotationDotsRow6_checked (j : Fin 30) :
    (rotationDotsRow6[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_6_0_checked
  · exact rotationDot_6_1_checked
  · exact rotationDot_6_2_checked
  · exact rotationDot_6_3_checked
  · exact rotationDot_6_4_checked
  · exact rotationDot_6_5_checked
  · exact rotationDot_6_6_checked
  · exact rotationDot_6_7_checked
  · exact rotationDot_6_8_checked
  · exact rotationDot_6_9_checked
  · exact rotationDot_6_10_checked
  · exact rotationDot_6_11_checked
  · exact rotationDot_6_12_checked
  · exact rotationDot_6_13_checked
  · exact rotationDot_6_14_checked
  · exact rotationDot_6_15_checked
  · exact rotationDot_6_16_checked
  · exact rotationDot_6_17_checked
  · exact rotationDot_6_18_checked
  · exact rotationDot_6_19_checked
  · exact rotationDot_6_20_checked
  · exact rotationDot_6_21_checked
  · exact rotationDot_6_22_checked
  · exact rotationDot_6_23_checked
  · exact rotationDot_6_24_checked
  · exact rotationDot_6_25_checked
  · exact rotationDot_6_26_checked
  · exact rotationDot_6_27_checked
  · exact rotationDot_6_28_checked
  · exact rotationDot_6_29_checked
def rotationDot_7_0 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_0_checked : rotationDot_7_0.ExtendedCheck nodes 3 := by decide
def rotationDot_7_1 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2156,11,11][i]?.getD 0
  accumulator := fun i => #[11,2156,2156,2156][i]?.getD 0
theorem rotationDot_7_1_checked : rotationDot_7_1.ExtendedCheck nodes 3 := by decide
def rotationDot_7_2 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_2_checked : rotationDot_7_2.ExtendedCheck nodes 3 := by decide
def rotationDot_7_3 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_3_checked : rotationDot_7_3.ExtendedCheck nodes 3 := by decide
def rotationDot_7_4 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_7_4_checked : rotationDot_7_4.ExtendedCheck nodes 3 := by decide
def rotationDot_7_5 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_5_checked : rotationDot_7_5.ExtendedCheck nodes 3 := by decide
def rotationDot_7_6 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_6_checked : rotationDot_7_6.ExtendedCheck nodes 3 := by decide
def rotationDot_7_7 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2158,11,36][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2159][i]?.getD 0
theorem rotationDot_7_7_checked : rotationDot_7_7.ExtendedCheck nodes 3 := by decide
def rotationDot_7_8 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_8_checked : rotationDot_7_8.ExtendedCheck nodes 3 := by decide
def rotationDot_7_9 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,2161][i]?.getD 0
  accumulator := fun i => #[11,11,11,2161][i]?.getD 0
theorem rotationDot_7_9_checked : rotationDot_7_9.ExtendedCheck nodes 3 := by decide
def rotationDot_7_10 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_7_10_checked : rotationDot_7_10.ExtendedCheck nodes 3 := by decide
def rotationDot_7_11 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2164,11,11][i]?.getD 0
  accumulator := fun i => #[11,2164,2164,2164][i]?.getD 0
theorem rotationDot_7_11_checked : rotationDot_7_11.ExtendedCheck nodes 3 := by decide
def rotationDot_7_12 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_12_checked : rotationDot_7_12.ExtendedCheck nodes 3 := by decide
def rotationDot_7_13 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2158,11,2161][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2166][i]?.getD 0
theorem rotationDot_7_13_checked : rotationDot_7_13.ExtendedCheck nodes 3 := by decide
def rotationDot_7_14 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_7_14_checked : rotationDot_7_14.ExtendedCheck nodes 3 := by decide
def rotationDot_7_15 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2168][i]?.getD 0
  accumulator := fun i => #[11,11,11,2168][i]?.getD 0
theorem rotationDot_7_15_checked : rotationDot_7_15.ExtendedCheck nodes 3 := by decide
def rotationDot_7_16 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_7_16_checked : rotationDot_7_16.ExtendedCheck nodes 3 := by decide
def rotationDot_7_17 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2171,11,11][i]?.getD 0
  accumulator := fun i => #[11,2171,2171,2171][i]?.getD 0
theorem rotationDot_7_17_checked : rotationDot_7_17.ExtendedCheck nodes 3 := by decide
def rotationDot_7_18 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2173][i]?.getD 0
  accumulator := fun i => #[11,11,11,2173][i]?.getD 0
theorem rotationDot_7_18_checked : rotationDot_7_18.ExtendedCheck nodes 3 := by decide
def rotationDot_7_19 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,2176][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2177][i]?.getD 0
theorem rotationDot_7_19_checked : rotationDot_7_19.ExtendedCheck nodes 3 := by decide
def rotationDot_7_20 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_7_20_checked : rotationDot_7_20.ExtendedCheck nodes 3 := by decide
def rotationDot_7_21 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2173][i]?.getD 0
  accumulator := fun i => #[11,11,11,2173][i]?.getD 0
theorem rotationDot_7_21_checked : rotationDot_7_21.ExtendedCheck nodes 3 := by decide
def rotationDot_7_22 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,2173][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2182][i]?.getD 0
theorem rotationDot_7_22_checked : rotationDot_7_22.ExtendedCheck nodes 3 := by decide
def rotationDot_7_23 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_7_23_checked : rotationDot_7_23.ExtendedCheck nodes 3 := by decide
def rotationDot_7_24 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2185][i]?.getD 0
  accumulator := fun i => #[11,11,11,2185][i]?.getD 0
theorem rotationDot_7_24_checked : rotationDot_7_24.ExtendedCheck nodes 3 := by decide
def rotationDot_7_25 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,2173][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2182][i]?.getD 0
theorem rotationDot_7_25_checked : rotationDot_7_25.ExtendedCheck nodes 3 := by decide
def rotationDot_7_26 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_7_26_checked : rotationDot_7_26.ExtendedCheck nodes 3 := by decide
def rotationDot_7_27 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2185][i]?.getD 0
  accumulator := fun i => #[11,11,11,2185][i]?.getD 0
theorem rotationDot_7_27_checked : rotationDot_7_27.ExtendedCheck nodes 3 := by decide
def rotationDot_7_28 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,2176][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2177][i]?.getD 0
theorem rotationDot_7_28_checked : rotationDot_7_28.ExtendedCheck nodes 3 := by decide
def rotationDot_7_29 : DotRecipe where
  left := fun i => #[12,11,5][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_7_29_checked : rotationDot_7_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow7 : Array DotRecipe := #[rotationDot_7_0,rotationDot_7_1,rotationDot_7_2,rotationDot_7_3,rotationDot_7_4,rotationDot_7_5,rotationDot_7_6,rotationDot_7_7,rotationDot_7_8,rotationDot_7_9,rotationDot_7_10,rotationDot_7_11,rotationDot_7_12,rotationDot_7_13,rotationDot_7_14,rotationDot_7_15,rotationDot_7_16,rotationDot_7_17,rotationDot_7_18,rotationDot_7_19,rotationDot_7_20,rotationDot_7_21,rotationDot_7_22,rotationDot_7_23,rotationDot_7_24,rotationDot_7_25,rotationDot_7_26,rotationDot_7_27,rotationDot_7_28,rotationDot_7_29]
theorem rotationDotsRow7_checked (j : Fin 30) :
    (rotationDotsRow7[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_7_0_checked
  · exact rotationDot_7_1_checked
  · exact rotationDot_7_2_checked
  · exact rotationDot_7_3_checked
  · exact rotationDot_7_4_checked
  · exact rotationDot_7_5_checked
  · exact rotationDot_7_6_checked
  · exact rotationDot_7_7_checked
  · exact rotationDot_7_8_checked
  · exact rotationDot_7_9_checked
  · exact rotationDot_7_10_checked
  · exact rotationDot_7_11_checked
  · exact rotationDot_7_12_checked
  · exact rotationDot_7_13_checked
  · exact rotationDot_7_14_checked
  · exact rotationDot_7_15_checked
  · exact rotationDot_7_16_checked
  · exact rotationDot_7_17_checked
  · exact rotationDot_7_18_checked
  · exact rotationDot_7_19_checked
  · exact rotationDot_7_20_checked
  · exact rotationDot_7_21_checked
  · exact rotationDot_7_22_checked
  · exact rotationDot_7_23_checked
  · exact rotationDot_7_24_checked
  · exact rotationDot_7_25_checked
  · exact rotationDot_7_26_checked
  · exact rotationDot_7_27_checked
  · exact rotationDot_7_28_checked
  · exact rotationDot_7_29_checked
def rotationDot_8_0 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,13,11][i]?.getD 0
  accumulator := fun i => #[11,11,13,13][i]?.getD 0
theorem rotationDot_8_0_checked : rotationDot_8_0.ExtendedCheck nodes 3 := by decide
def rotationDot_8_1 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_1_checked : rotationDot_8_1.ExtendedCheck nodes 3 := by decide
def rotationDot_8_2 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_2_checked : rotationDot_8_2.ExtendedCheck nodes 3 := by decide
def rotationDot_8_3 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2194,11][i]?.getD 0
  accumulator := fun i => #[11,11,2194,2194][i]?.getD 0
theorem rotationDot_8_3_checked : rotationDot_8_3.ExtendedCheck nodes 3 := by decide
def rotationDot_8_4 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_4_checked : rotationDot_8_4.ExtendedCheck nodes 3 := by decide
def rotationDot_8_5 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_5_checked : rotationDot_8_5.ExtendedCheck nodes 3 := by decide
def rotationDot_8_6 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2196,11][i]?.getD 0
  accumulator := fun i => #[11,11,2196,2196][i]?.getD 0
theorem rotationDot_8_6_checked : rotationDot_8_6.ExtendedCheck nodes 3 := by decide
def rotationDot_8_7 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_7_checked : rotationDot_8_7.ExtendedCheck nodes 3 := by decide
def rotationDot_8_8 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,113,11][i]?.getD 0
  accumulator := fun i => #[11,11,113,113][i]?.getD 0
theorem rotationDot_8_8_checked : rotationDot_8_8.ExtendedCheck nodes 3 := by decide
def rotationDot_8_9 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2196,11][i]?.getD 0
  accumulator := fun i => #[11,11,2196,2196][i]?.getD 0
theorem rotationDot_8_9_checked : rotationDot_8_9.ExtendedCheck nodes 3 := by decide
def rotationDot_8_10 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_10_checked : rotationDot_8_10.ExtendedCheck nodes 3 := by decide
def rotationDot_8_11 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_11_checked : rotationDot_8_11.ExtendedCheck nodes 3 := by decide
def rotationDot_8_12 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2196,11][i]?.getD 0
  accumulator := fun i => #[11,11,2196,2196][i]?.getD 0
theorem rotationDot_8_12_checked : rotationDot_8_12.ExtendedCheck nodes 3 := by decide
def rotationDot_8_13 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_13_checked : rotationDot_8_13.ExtendedCheck nodes 3 := by decide
def rotationDot_8_14 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2201,11][i]?.getD 0
  accumulator := fun i => #[11,11,2201,2201][i]?.getD 0
theorem rotationDot_8_14_checked : rotationDot_8_14.ExtendedCheck nodes 3 := by decide
def rotationDot_8_15 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2196,11][i]?.getD 0
  accumulator := fun i => #[11,11,2196,2196][i]?.getD 0
theorem rotationDot_8_15_checked : rotationDot_8_15.ExtendedCheck nodes 3 := by decide
def rotationDot_8_16 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_16_checked : rotationDot_8_16.ExtendedCheck nodes 3 := by decide
def rotationDot_8_17 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_17_checked : rotationDot_8_17.ExtendedCheck nodes 3 := by decide
def rotationDot_8_18 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2204,11][i]?.getD 0
  accumulator := fun i => #[11,11,2204,2204][i]?.getD 0
theorem rotationDot_8_18_checked : rotationDot_8_18.ExtendedCheck nodes 3 := by decide
def rotationDot_8_19 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_19_checked : rotationDot_8_19.ExtendedCheck nodes 3 := by decide
def rotationDot_8_20 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2206,11][i]?.getD 0
  accumulator := fun i => #[11,11,2206,2206][i]?.getD 0
theorem rotationDot_8_20_checked : rotationDot_8_20.ExtendedCheck nodes 3 := by decide
def rotationDot_8_21 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2204,11][i]?.getD 0
  accumulator := fun i => #[11,11,2204,2204][i]?.getD 0
theorem rotationDot_8_21_checked : rotationDot_8_21.ExtendedCheck nodes 3 := by decide
def rotationDot_8_22 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_22_checked : rotationDot_8_22.ExtendedCheck nodes 3 := by decide
def rotationDot_8_23 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2209,11][i]?.getD 0
  accumulator := fun i => #[11,11,2209,2209][i]?.getD 0
theorem rotationDot_8_23_checked : rotationDot_8_23.ExtendedCheck nodes 3 := by decide
def rotationDot_8_24 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2204,11][i]?.getD 0
  accumulator := fun i => #[11,11,2204,2204][i]?.getD 0
theorem rotationDot_8_24_checked : rotationDot_8_24.ExtendedCheck nodes 3 := by decide
def rotationDot_8_25 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_25_checked : rotationDot_8_25.ExtendedCheck nodes 3 := by decide
def rotationDot_8_26 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2209,11][i]?.getD 0
  accumulator := fun i => #[11,11,2209,2209][i]?.getD 0
theorem rotationDot_8_26_checked : rotationDot_8_26.ExtendedCheck nodes 3 := by decide
def rotationDot_8_27 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2204,11][i]?.getD 0
  accumulator := fun i => #[11,11,2204,2204][i]?.getD 0
theorem rotationDot_8_27_checked : rotationDot_8_27.ExtendedCheck nodes 3 := by decide
def rotationDot_8_28 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_8_28_checked : rotationDot_8_28.ExtendedCheck nodes 3 := by decide
def rotationDot_8_29 : DotRecipe where
  left := fun i => #[11,13,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2206,11][i]?.getD 0
  accumulator := fun i => #[11,11,2206,2206][i]?.getD 0
theorem rotationDot_8_29_checked : rotationDot_8_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow8 : Array DotRecipe := #[rotationDot_8_0,rotationDot_8_1,rotationDot_8_2,rotationDot_8_3,rotationDot_8_4,rotationDot_8_5,rotationDot_8_6,rotationDot_8_7,rotationDot_8_8,rotationDot_8_9,rotationDot_8_10,rotationDot_8_11,rotationDot_8_12,rotationDot_8_13,rotationDot_8_14,rotationDot_8_15,rotationDot_8_16,rotationDot_8_17,rotationDot_8_18,rotationDot_8_19,rotationDot_8_20,rotationDot_8_21,rotationDot_8_22,rotationDot_8_23,rotationDot_8_24,rotationDot_8_25,rotationDot_8_26,rotationDot_8_27,rotationDot_8_28,rotationDot_8_29]
theorem rotationDotsRow8_checked (j : Fin 30) :
    (rotationDotsRow8[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_8_0_checked
  · exact rotationDot_8_1_checked
  · exact rotationDot_8_2_checked
  · exact rotationDot_8_3_checked
  · exact rotationDot_8_4_checked
  · exact rotationDot_8_5_checked
  · exact rotationDot_8_6_checked
  · exact rotationDot_8_7_checked
  · exact rotationDot_8_8_checked
  · exact rotationDot_8_9_checked
  · exact rotationDot_8_10_checked
  · exact rotationDot_8_11_checked
  · exact rotationDot_8_12_checked
  · exact rotationDot_8_13_checked
  · exact rotationDot_8_14_checked
  · exact rotationDot_8_15_checked
  · exact rotationDot_8_16_checked
  · exact rotationDot_8_17_checked
  · exact rotationDot_8_18_checked
  · exact rotationDot_8_19_checked
  · exact rotationDot_8_20_checked
  · exact rotationDot_8_21_checked
  · exact rotationDot_8_22_checked
  · exact rotationDot_8_23_checked
  · exact rotationDot_8_24_checked
  · exact rotationDot_8_25_checked
  · exact rotationDot_8_26_checked
  · exact rotationDot_8_27_checked
  · exact rotationDot_8_28_checked
  · exact rotationDot_8_29_checked
def rotationDot_9_0 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_9_0_checked : rotationDot_9_0.ExtendedCheck nodes 3 := by decide
def rotationDot_9_1 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_1_checked : rotationDot_9_1.ExtendedCheck nodes 3 := by decide
def rotationDot_9_2 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_2_checked : rotationDot_9_2.ExtendedCheck nodes 3 := by decide
def rotationDot_9_3 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2135,11][i]?.getD 0
  accumulator := fun i => #[11,11,2135,2135][i]?.getD 0
theorem rotationDot_9_3_checked : rotationDot_9_3.ExtendedCheck nodes 3 := by decide
def rotationDot_9_4 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_4_checked : rotationDot_9_4.ExtendedCheck nodes 3 := by decide
def rotationDot_9_5 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_5_checked : rotationDot_9_5.ExtendedCheck nodes 3 := by decide
def rotationDot_9_6 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_9_6_checked : rotationDot_9_6.ExtendedCheck nodes 3 := by decide
def rotationDot_9_7 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2216][i]?.getD 0
  accumulator := fun i => #[11,11,11,2216][i]?.getD 0
theorem rotationDot_9_7_checked : rotationDot_9_7.ExtendedCheck nodes 3 := by decide
def rotationDot_9_8 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2138,11][i]?.getD 0
  accumulator := fun i => #[11,11,2138,2138][i]?.getD 0
theorem rotationDot_9_8_checked : rotationDot_9_8.ExtendedCheck nodes 3 := by decide
def rotationDot_9_9 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,1,113][i]?.getD 0
  accumulator := fun i => #[11,11,1,2219][i]?.getD 0
theorem rotationDot_9_9_checked : rotationDot_9_9.ExtendedCheck nodes 3 := by decide
def rotationDot_9_10 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_10_checked : rotationDot_9_10.ExtendedCheck nodes 3 := by decide
def rotationDot_9_11 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_11_checked : rotationDot_9_11.ExtendedCheck nodes 3 := by decide
def rotationDot_9_12 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_9_12_checked : rotationDot_9_12.ExtendedCheck nodes 3 := by decide
def rotationDot_9_13 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,113][i]?.getD 0
  accumulator := fun i => #[11,11,11,113][i]?.getD 0
theorem rotationDot_9_13_checked : rotationDot_9_13.ExtendedCheck nodes 3 := by decide
def rotationDot_9_14 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2142,11][i]?.getD 0
  accumulator := fun i => #[11,11,2142,2142][i]?.getD 0
theorem rotationDot_9_14_checked : rotationDot_9_14.ExtendedCheck nodes 3 := by decide
def rotationDot_9_15 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,1,2201][i]?.getD 0
  accumulator := fun i => #[11,11,1,2223][i]?.getD 0
theorem rotationDot_9_15_checked : rotationDot_9_15.ExtendedCheck nodes 3 := by decide
def rotationDot_9_16 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_16_checked : rotationDot_9_16.ExtendedCheck nodes 3 := by decide
def rotationDot_9_17 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_9_17_checked : rotationDot_9_17.ExtendedCheck nodes 3 := by decide
def rotationDot_9_18 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,2206][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2225][i]?.getD 0
theorem rotationDot_9_18_checked : rotationDot_9_18.ExtendedCheck nodes 3 := by decide
def rotationDot_9_19 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2227][i]?.getD 0
  accumulator := fun i => #[11,11,11,2227][i]?.getD 0
theorem rotationDot_9_19_checked : rotationDot_9_19.ExtendedCheck nodes 3 := by decide
def rotationDot_9_20 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_9_20_checked : rotationDot_9_20.ExtendedCheck nodes 3 := by decide
def rotationDot_9_21 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,2206][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2225][i]?.getD 0
theorem rotationDot_9_21_checked : rotationDot_9_21.ExtendedCheck nodes 3 := by decide
def rotationDot_9_22 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2206][i]?.getD 0
  accumulator := fun i => #[11,11,11,2206][i]?.getD 0
theorem rotationDot_9_22_checked : rotationDot_9_22.ExtendedCheck nodes 3 := by decide
def rotationDot_9_23 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_9_23_checked : rotationDot_9_23.ExtendedCheck nodes 3 := by decide
def rotationDot_9_24 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,2209][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2233][i]?.getD 0
theorem rotationDot_9_24_checked : rotationDot_9_24.ExtendedCheck nodes 3 := by decide
def rotationDot_9_25 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2206][i]?.getD 0
  accumulator := fun i => #[11,11,11,2206][i]?.getD 0
theorem rotationDot_9_25_checked : rotationDot_9_25.ExtendedCheck nodes 3 := by decide
def rotationDot_9_26 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_9_26_checked : rotationDot_9_26.ExtendedCheck nodes 3 := by decide
def rotationDot_9_27 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,2209][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2233][i]?.getD 0
theorem rotationDot_9_27_checked : rotationDot_9_27.ExtendedCheck nodes 3 := by decide
def rotationDot_9_28 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2227][i]?.getD 0
  accumulator := fun i => #[11,11,11,2227][i]?.getD 0
theorem rotationDot_9_28_checked : rotationDot_9_28.ExtendedCheck nodes 3 := by decide
def rotationDot_9_29 : DotRecipe where
  left := fun i => #[11,0,13][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_9_29_checked : rotationDot_9_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow9 : Array DotRecipe := #[rotationDot_9_0,rotationDot_9_1,rotationDot_9_2,rotationDot_9_3,rotationDot_9_4,rotationDot_9_5,rotationDot_9_6,rotationDot_9_7,rotationDot_9_8,rotationDot_9_9,rotationDot_9_10,rotationDot_9_11,rotationDot_9_12,rotationDot_9_13,rotationDot_9_14,rotationDot_9_15,rotationDot_9_16,rotationDot_9_17,rotationDot_9_18,rotationDot_9_19,rotationDot_9_20,rotationDot_9_21,rotationDot_9_22,rotationDot_9_23,rotationDot_9_24,rotationDot_9_25,rotationDot_9_26,rotationDot_9_27,rotationDot_9_28,rotationDot_9_29]
theorem rotationDotsRow9_checked (j : Fin 30) :
    (rotationDotsRow9[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_9_0_checked
  · exact rotationDot_9_1_checked
  · exact rotationDot_9_2_checked
  · exact rotationDot_9_3_checked
  · exact rotationDot_9_4_checked
  · exact rotationDot_9_5_checked
  · exact rotationDot_9_6_checked
  · exact rotationDot_9_7_checked
  · exact rotationDot_9_8_checked
  · exact rotationDot_9_9_checked
  · exact rotationDot_9_10_checked
  · exact rotationDot_9_11_checked
  · exact rotationDot_9_12_checked
  · exact rotationDot_9_13_checked
  · exact rotationDot_9_14_checked
  · exact rotationDot_9_15_checked
  · exact rotationDot_9_16_checked
  · exact rotationDot_9_17_checked
  · exact rotationDot_9_18_checked
  · exact rotationDot_9_19_checked
  · exact rotationDot_9_20_checked
  · exact rotationDot_9_21_checked
  · exact rotationDot_9_22_checked
  · exact rotationDot_9_23_checked
  · exact rotationDot_9_24_checked
  · exact rotationDot_9_25_checked
  · exact rotationDot_9_26_checked
  · exact rotationDot_9_27_checked
  · exact rotationDot_9_28_checked
  · exact rotationDot_9_29_checked
def rotationDot_10_0 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_0_checked : rotationDot_10_0.ExtendedCheck nodes 3 := by decide
def rotationDot_10_1 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2156,11,11][i]?.getD 0
  accumulator := fun i => #[11,2156,2156,2156][i]?.getD 0
theorem rotationDot_10_1_checked : rotationDot_10_1.ExtendedCheck nodes 3 := by decide
def rotationDot_10_2 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_2_checked : rotationDot_10_2.ExtendedCheck nodes 3 := by decide
def rotationDot_10_3 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_3_checked : rotationDot_10_3.ExtendedCheck nodes 3 := by decide
def rotationDot_10_4 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_10_4_checked : rotationDot_10_4.ExtendedCheck nodes 3 := by decide
def rotationDot_10_5 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_5_checked : rotationDot_10_5.ExtendedCheck nodes 3 := by decide
def rotationDot_10_6 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_6_checked : rotationDot_10_6.ExtendedCheck nodes 3 := by decide
def rotationDot_10_7 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_10_7_checked : rotationDot_10_7.ExtendedCheck nodes 3 := by decide
def rotationDot_10_8 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_8_checked : rotationDot_10_8.ExtendedCheck nodes 3 := by decide
def rotationDot_10_9 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_9_checked : rotationDot_10_9.ExtendedCheck nodes 3 := by decide
def rotationDot_10_10 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_10_10_checked : rotationDot_10_10.ExtendedCheck nodes 3 := by decide
def rotationDot_10_11 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2164,11,11][i]?.getD 0
  accumulator := fun i => #[11,2164,2164,2164][i]?.getD 0
theorem rotationDot_10_11_checked : rotationDot_10_11.ExtendedCheck nodes 3 := by decide
def rotationDot_10_12 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_12_checked : rotationDot_10_12.ExtendedCheck nodes 3 := by decide
def rotationDot_10_13 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_10_13_checked : rotationDot_10_13.ExtendedCheck nodes 3 := by decide
def rotationDot_10_14 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_14_checked : rotationDot_10_14.ExtendedCheck nodes 3 := by decide
def rotationDot_10_15 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_15_checked : rotationDot_10_15.ExtendedCheck nodes 3 := by decide
def rotationDot_10_16 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_10_16_checked : rotationDot_10_16.ExtendedCheck nodes 3 := by decide
def rotationDot_10_17 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2171,11,11][i]?.getD 0
  accumulator := fun i => #[11,2171,2171,2171][i]?.getD 0
theorem rotationDot_10_17_checked : rotationDot_10_17.ExtendedCheck nodes 3 := by decide
def rotationDot_10_18 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_18_checked : rotationDot_10_18.ExtendedCheck nodes 3 := by decide
def rotationDot_10_19 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_10_19_checked : rotationDot_10_19.ExtendedCheck nodes 3 := by decide
def rotationDot_10_20 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_10_20_checked : rotationDot_10_20.ExtendedCheck nodes 3 := by decide
def rotationDot_10_21 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_21_checked : rotationDot_10_21.ExtendedCheck nodes 3 := by decide
def rotationDot_10_22 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_10_22_checked : rotationDot_10_22.ExtendedCheck nodes 3 := by decide
def rotationDot_10_23 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_10_23_checked : rotationDot_10_23.ExtendedCheck nodes 3 := by decide
def rotationDot_10_24 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_24_checked : rotationDot_10_24.ExtendedCheck nodes 3 := by decide
def rotationDot_10_25 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_10_25_checked : rotationDot_10_25.ExtendedCheck nodes 3 := by decide
def rotationDot_10_26 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_10_26_checked : rotationDot_10_26.ExtendedCheck nodes 3 := by decide
def rotationDot_10_27 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_10_27_checked : rotationDot_10_27.ExtendedCheck nodes 3 := by decide
def rotationDot_10_28 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_10_28_checked : rotationDot_10_28.ExtendedCheck nodes 3 := by decide
def rotationDot_10_29 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_10_29_checked : rotationDot_10_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow10 : Array DotRecipe := #[rotationDot_10_0,rotationDot_10_1,rotationDot_10_2,rotationDot_10_3,rotationDot_10_4,rotationDot_10_5,rotationDot_10_6,rotationDot_10_7,rotationDot_10_8,rotationDot_10_9,rotationDot_10_10,rotationDot_10_11,rotationDot_10_12,rotationDot_10_13,rotationDot_10_14,rotationDot_10_15,rotationDot_10_16,rotationDot_10_17,rotationDot_10_18,rotationDot_10_19,rotationDot_10_20,rotationDot_10_21,rotationDot_10_22,rotationDot_10_23,rotationDot_10_24,rotationDot_10_25,rotationDot_10_26,rotationDot_10_27,rotationDot_10_28,rotationDot_10_29]
theorem rotationDotsRow10_checked (j : Fin 30) :
    (rotationDotsRow10[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_10_0_checked
  · exact rotationDot_10_1_checked
  · exact rotationDot_10_2_checked
  · exact rotationDot_10_3_checked
  · exact rotationDot_10_4_checked
  · exact rotationDot_10_5_checked
  · exact rotationDot_10_6_checked
  · exact rotationDot_10_7_checked
  · exact rotationDot_10_8_checked
  · exact rotationDot_10_9_checked
  · exact rotationDot_10_10_checked
  · exact rotationDot_10_11_checked
  · exact rotationDot_10_12_checked
  · exact rotationDot_10_13_checked
  · exact rotationDot_10_14_checked
  · exact rotationDot_10_15_checked
  · exact rotationDot_10_16_checked
  · exact rotationDot_10_17_checked
  · exact rotationDot_10_18_checked
  · exact rotationDot_10_19_checked
  · exact rotationDot_10_20_checked
  · exact rotationDot_10_21_checked
  · exact rotationDot_10_22_checked
  · exact rotationDot_10_23_checked
  · exact rotationDot_10_24_checked
  · exact rotationDot_10_25_checked
  · exact rotationDot_10_26_checked
  · exact rotationDot_10_27_checked
  · exact rotationDot_10_28_checked
  · exact rotationDot_10_29_checked
def rotationDot_11_0 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_0_checked : rotationDot_11_0.ExtendedCheck nodes 3 := by decide
def rotationDot_11_1 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2253,11,11][i]?.getD 0
  accumulator := fun i => #[11,2253,2253,2253][i]?.getD 0
theorem rotationDot_11_1_checked : rotationDot_11_1.ExtendedCheck nodes 3 := by decide
def rotationDot_11_2 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_2_checked : rotationDot_11_2.ExtendedCheck nodes 3 := by decide
def rotationDot_11_3 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_3_checked : rotationDot_11_3.ExtendedCheck nodes 3 := by decide
def rotationDot_11_4 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[5,11,11][i]?.getD 0
  accumulator := fun i => #[11,5,5,5][i]?.getD 0
theorem rotationDot_11_4_checked : rotationDot_11_4.ExtendedCheck nodes 3 := by decide
def rotationDot_11_5 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_5_checked : rotationDot_11_5.ExtendedCheck nodes 3 := by decide
def rotationDot_11_6 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_6_checked : rotationDot_11_6.ExtendedCheck nodes 3 := by decide
def rotationDot_11_7 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2256,11,11][i]?.getD 0
  accumulator := fun i => #[11,2256,2256,2256][i]?.getD 0
theorem rotationDot_11_7_checked : rotationDot_11_7.ExtendedCheck nodes 3 := by decide
def rotationDot_11_8 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_8_checked : rotationDot_11_8.ExtendedCheck nodes 3 := by decide
def rotationDot_11_9 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_9_checked : rotationDot_11_9.ExtendedCheck nodes 3 := by decide
def rotationDot_11_10 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2256,11,11][i]?.getD 0
  accumulator := fun i => #[11,2256,2256,2256][i]?.getD 0
theorem rotationDot_11_10_checked : rotationDot_11_10.ExtendedCheck nodes 3 := by decide
def rotationDot_11_11 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[36,11,11][i]?.getD 0
  accumulator := fun i => #[11,36,36,36][i]?.getD 0
theorem rotationDot_11_11_checked : rotationDot_11_11.ExtendedCheck nodes 3 := by decide
def rotationDot_11_12 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_12_checked : rotationDot_11_12.ExtendedCheck nodes 3 := by decide
def rotationDot_11_13 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2256,11,11][i]?.getD 0
  accumulator := fun i => #[11,2256,2256,2256][i]?.getD 0
theorem rotationDot_11_13_checked : rotationDot_11_13.ExtendedCheck nodes 3 := by decide
def rotationDot_11_14 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_14_checked : rotationDot_11_14.ExtendedCheck nodes 3 := by decide
def rotationDot_11_15 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_15_checked : rotationDot_11_15.ExtendedCheck nodes 3 := by decide
def rotationDot_11_16 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2256,11,11][i]?.getD 0
  accumulator := fun i => #[11,2256,2256,2256][i]?.getD 0
theorem rotationDot_11_16_checked : rotationDot_11_16.ExtendedCheck nodes 3 := by decide
def rotationDot_11_17 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2161,11,11][i]?.getD 0
  accumulator := fun i => #[11,2161,2161,2161][i]?.getD 0
theorem rotationDot_11_17_checked : rotationDot_11_17.ExtendedCheck nodes 3 := by decide
def rotationDot_11_18 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_18_checked : rotationDot_11_18.ExtendedCheck nodes 3 := by decide
def rotationDot_11_19 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2263,11,11][i]?.getD 0
  accumulator := fun i => #[11,2263,2263,2263][i]?.getD 0
theorem rotationDot_11_19_checked : rotationDot_11_19.ExtendedCheck nodes 3 := by decide
def rotationDot_11_20 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2176,11,11][i]?.getD 0
  accumulator := fun i => #[11,2176,2176,2176][i]?.getD 0
theorem rotationDot_11_20_checked : rotationDot_11_20.ExtendedCheck nodes 3 := by decide
def rotationDot_11_21 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_21_checked : rotationDot_11_21.ExtendedCheck nodes 3 := by decide
def rotationDot_11_22 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2263,11,11][i]?.getD 0
  accumulator := fun i => #[11,2263,2263,2263][i]?.getD 0
theorem rotationDot_11_22_checked : rotationDot_11_22.ExtendedCheck nodes 3 := by decide
def rotationDot_11_23 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2176,11,11][i]?.getD 0
  accumulator := fun i => #[11,2176,2176,2176][i]?.getD 0
theorem rotationDot_11_23_checked : rotationDot_11_23.ExtendedCheck nodes 3 := by decide
def rotationDot_11_24 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_24_checked : rotationDot_11_24.ExtendedCheck nodes 3 := by decide
def rotationDot_11_25 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2263,11,11][i]?.getD 0
  accumulator := fun i => #[11,2263,2263,2263][i]?.getD 0
theorem rotationDot_11_25_checked : rotationDot_11_25.ExtendedCheck nodes 3 := by decide
def rotationDot_11_26 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2173,11,11][i]?.getD 0
  accumulator := fun i => #[11,2173,2173,2173][i]?.getD 0
theorem rotationDot_11_26_checked : rotationDot_11_26.ExtendedCheck nodes 3 := by decide
def rotationDot_11_27 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_11_27_checked : rotationDot_11_27.ExtendedCheck nodes 3 := by decide
def rotationDot_11_28 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2263,11,11][i]?.getD 0
  accumulator := fun i => #[11,2263,2263,2263][i]?.getD 0
theorem rotationDot_11_28_checked : rotationDot_11_28.ExtendedCheck nodes 3 := by decide
def rotationDot_11_29 : DotRecipe where
  left := fun i => #[5,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2173,11,11][i]?.getD 0
  accumulator := fun i => #[11,2173,2173,2173][i]?.getD 0
theorem rotationDot_11_29_checked : rotationDot_11_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow11 : Array DotRecipe := #[rotationDot_11_0,rotationDot_11_1,rotationDot_11_2,rotationDot_11_3,rotationDot_11_4,rotationDot_11_5,rotationDot_11_6,rotationDot_11_7,rotationDot_11_8,rotationDot_11_9,rotationDot_11_10,rotationDot_11_11,rotationDot_11_12,rotationDot_11_13,rotationDot_11_14,rotationDot_11_15,rotationDot_11_16,rotationDot_11_17,rotationDot_11_18,rotationDot_11_19,rotationDot_11_20,rotationDot_11_21,rotationDot_11_22,rotationDot_11_23,rotationDot_11_24,rotationDot_11_25,rotationDot_11_26,rotationDot_11_27,rotationDot_11_28,rotationDot_11_29]
theorem rotationDotsRow11_checked (j : Fin 30) :
    (rotationDotsRow11[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_11_0_checked
  · exact rotationDot_11_1_checked
  · exact rotationDot_11_2_checked
  · exact rotationDot_11_3_checked
  · exact rotationDot_11_4_checked
  · exact rotationDot_11_5_checked
  · exact rotationDot_11_6_checked
  · exact rotationDot_11_7_checked
  · exact rotationDot_11_8_checked
  · exact rotationDot_11_9_checked
  · exact rotationDot_11_10_checked
  · exact rotationDot_11_11_checked
  · exact rotationDot_11_12_checked
  · exact rotationDot_11_13_checked
  · exact rotationDot_11_14_checked
  · exact rotationDot_11_15_checked
  · exact rotationDot_11_16_checked
  · exact rotationDot_11_17_checked
  · exact rotationDot_11_18_checked
  · exact rotationDot_11_19_checked
  · exact rotationDot_11_20_checked
  · exact rotationDot_11_21_checked
  · exact rotationDot_11_22_checked
  · exact rotationDot_11_23_checked
  · exact rotationDot_11_24_checked
  · exact rotationDot_11_25_checked
  · exact rotationDot_11_26_checked
  · exact rotationDot_11_27_checked
  · exact rotationDot_11_28_checked
  · exact rotationDot_11_29_checked
def rotationDot_12_0 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_12_0_checked : rotationDot_12_0.ExtendedCheck nodes 3 := by decide
def rotationDot_12_1 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_1_checked : rotationDot_12_1.ExtendedCheck nodes 3 := by decide
def rotationDot_12_2 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_2_checked : rotationDot_12_2.ExtendedCheck nodes 3 := by decide
def rotationDot_12_3 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2135,11][i]?.getD 0
  accumulator := fun i => #[11,11,2135,2135][i]?.getD 0
theorem rotationDot_12_3_checked : rotationDot_12_3.ExtendedCheck nodes 3 := by decide
def rotationDot_12_4 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_4_checked : rotationDot_12_4.ExtendedCheck nodes 3 := by decide
def rotationDot_12_5 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_5_checked : rotationDot_12_5.ExtendedCheck nodes 3 := by decide
def rotationDot_12_6 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_12_6_checked : rotationDot_12_6.ExtendedCheck nodes 3 := by decide
def rotationDot_12_7 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_7_checked : rotationDot_12_7.ExtendedCheck nodes 3 := by decide
def rotationDot_12_8 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2138,11][i]?.getD 0
  accumulator := fun i => #[11,11,2138,2138][i]?.getD 0
theorem rotationDot_12_8_checked : rotationDot_12_8.ExtendedCheck nodes 3 := by decide
def rotationDot_12_9 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_12_9_checked : rotationDot_12_9.ExtendedCheck nodes 3 := by decide
def rotationDot_12_10 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_10_checked : rotationDot_12_10.ExtendedCheck nodes 3 := by decide
def rotationDot_12_11 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_11_checked : rotationDot_12_11.ExtendedCheck nodes 3 := by decide
def rotationDot_12_12 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_12_12_checked : rotationDot_12_12.ExtendedCheck nodes 3 := by decide
def rotationDot_12_13 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_13_checked : rotationDot_12_13.ExtendedCheck nodes 3 := by decide
def rotationDot_12_14 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2142,11][i]?.getD 0
  accumulator := fun i => #[11,11,2142,2142][i]?.getD 0
theorem rotationDot_12_14_checked : rotationDot_12_14.ExtendedCheck nodes 3 := by decide
def rotationDot_12_15 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_12_15_checked : rotationDot_12_15.ExtendedCheck nodes 3 := by decide
def rotationDot_12_16 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_16_checked : rotationDot_12_16.ExtendedCheck nodes 3 := by decide
def rotationDot_12_17 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_17_checked : rotationDot_12_17.ExtendedCheck nodes 3 := by decide
def rotationDot_12_18 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_12_18_checked : rotationDot_12_18.ExtendedCheck nodes 3 := by decide
def rotationDot_12_19 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_19_checked : rotationDot_12_19.ExtendedCheck nodes 3 := by decide
def rotationDot_12_20 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_12_20_checked : rotationDot_12_20.ExtendedCheck nodes 3 := by decide
def rotationDot_12_21 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_12_21_checked : rotationDot_12_21.ExtendedCheck nodes 3 := by decide
def rotationDot_12_22 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_22_checked : rotationDot_12_22.ExtendedCheck nodes 3 := by decide
def rotationDot_12_23 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_12_23_checked : rotationDot_12_23.ExtendedCheck nodes 3 := by decide
def rotationDot_12_24 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_12_24_checked : rotationDot_12_24.ExtendedCheck nodes 3 := by decide
def rotationDot_12_25 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_25_checked : rotationDot_12_25.ExtendedCheck nodes 3 := by decide
def rotationDot_12_26 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_12_26_checked : rotationDot_12_26.ExtendedCheck nodes 3 := by decide
def rotationDot_12_27 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,11][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2145][i]?.getD 0
theorem rotationDot_12_27_checked : rotationDot_12_27.ExtendedCheck nodes 3 := by decide
def rotationDot_12_28 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_12_28_checked : rotationDot_12_28.ExtendedCheck nodes 3 := by decide
def rotationDot_12_29 : DotRecipe where
  left := fun i => #[11,0,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_12_29_checked : rotationDot_12_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow12 : Array DotRecipe := #[rotationDot_12_0,rotationDot_12_1,rotationDot_12_2,rotationDot_12_3,rotationDot_12_4,rotationDot_12_5,rotationDot_12_6,rotationDot_12_7,rotationDot_12_8,rotationDot_12_9,rotationDot_12_10,rotationDot_12_11,rotationDot_12_12,rotationDot_12_13,rotationDot_12_14,rotationDot_12_15,rotationDot_12_16,rotationDot_12_17,rotationDot_12_18,rotationDot_12_19,rotationDot_12_20,rotationDot_12_21,rotationDot_12_22,rotationDot_12_23,rotationDot_12_24,rotationDot_12_25,rotationDot_12_26,rotationDot_12_27,rotationDot_12_28,rotationDot_12_29]
theorem rotationDotsRow12_checked (j : Fin 30) :
    (rotationDotsRow12[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_12_0_checked
  · exact rotationDot_12_1_checked
  · exact rotationDot_12_2_checked
  · exact rotationDot_12_3_checked
  · exact rotationDot_12_4_checked
  · exact rotationDot_12_5_checked
  · exact rotationDot_12_6_checked
  · exact rotationDot_12_7_checked
  · exact rotationDot_12_8_checked
  · exact rotationDot_12_9_checked
  · exact rotationDot_12_10_checked
  · exact rotationDot_12_11_checked
  · exact rotationDot_12_12_checked
  · exact rotationDot_12_13_checked
  · exact rotationDot_12_14_checked
  · exact rotationDot_12_15_checked
  · exact rotationDot_12_16_checked
  · exact rotationDot_12_17_checked
  · exact rotationDot_12_18_checked
  · exact rotationDot_12_19_checked
  · exact rotationDot_12_20_checked
  · exact rotationDot_12_21_checked
  · exact rotationDot_12_22_checked
  · exact rotationDot_12_23_checked
  · exact rotationDot_12_24_checked
  · exact rotationDot_12_25_checked
  · exact rotationDot_12_26_checked
  · exact rotationDot_12_27_checked
  · exact rotationDot_12_28_checked
  · exact rotationDot_12_29_checked
def rotationDot_13_0 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_0_checked : rotationDot_13_0.ExtendedCheck nodes 3 := by decide
def rotationDot_13_1 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2156,11,11][i]?.getD 0
  accumulator := fun i => #[11,2156,2156,2156][i]?.getD 0
theorem rotationDot_13_1_checked : rotationDot_13_1.ExtendedCheck nodes 3 := by decide
def rotationDot_13_2 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_2_checked : rotationDot_13_2.ExtendedCheck nodes 3 := by decide
def rotationDot_13_3 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_3_checked : rotationDot_13_3.ExtendedCheck nodes 3 := by decide
def rotationDot_13_4 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_13_4_checked : rotationDot_13_4.ExtendedCheck nodes 3 := by decide
def rotationDot_13_5 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_5_checked : rotationDot_13_5.ExtendedCheck nodes 3 := by decide
def rotationDot_13_6 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_6_checked : rotationDot_13_6.ExtendedCheck nodes 3 := by decide
def rotationDot_13_7 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2158,11,2216][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2286][i]?.getD 0
theorem rotationDot_13_7_checked : rotationDot_13_7.ExtendedCheck nodes 3 := by decide
def rotationDot_13_8 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_8_checked : rotationDot_13_8.ExtendedCheck nodes 3 := by decide
def rotationDot_13_9 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,113][i]?.getD 0
  accumulator := fun i => #[11,11,11,113][i]?.getD 0
theorem rotationDot_13_9_checked : rotationDot_13_9.ExtendedCheck nodes 3 := by decide
def rotationDot_13_10 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_13_10_checked : rotationDot_13_10.ExtendedCheck nodes 3 := by decide
def rotationDot_13_11 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2164,11,11][i]?.getD 0
  accumulator := fun i => #[11,2164,2164,2164][i]?.getD 0
theorem rotationDot_13_11_checked : rotationDot_13_11.ExtendedCheck nodes 3 := by decide
def rotationDot_13_12 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_12_checked : rotationDot_13_12.ExtendedCheck nodes 3 := by decide
def rotationDot_13_13 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2158,11,113][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2289][i]?.getD 0
theorem rotationDot_13_13_checked : rotationDot_13_13.ExtendedCheck nodes 3 := by decide
def rotationDot_13_14 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_13_14_checked : rotationDot_13_14.ExtendedCheck nodes 3 := by decide
def rotationDot_13_15 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2201][i]?.getD 0
  accumulator := fun i => #[11,11,11,2201][i]?.getD 0
theorem rotationDot_13_15_checked : rotationDot_13_15.ExtendedCheck nodes 3 := by decide
def rotationDot_13_16 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_13_16_checked : rotationDot_13_16.ExtendedCheck nodes 3 := by decide
def rotationDot_13_17 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2171,11,11][i]?.getD 0
  accumulator := fun i => #[11,2171,2171,2171][i]?.getD 0
theorem rotationDot_13_17_checked : rotationDot_13_17.ExtendedCheck nodes 3 := by decide
def rotationDot_13_18 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2206][i]?.getD 0
  accumulator := fun i => #[11,11,11,2206][i]?.getD 0
theorem rotationDot_13_18_checked : rotationDot_13_18.ExtendedCheck nodes 3 := by decide
def rotationDot_13_19 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,2227][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2295][i]?.getD 0
theorem rotationDot_13_19_checked : rotationDot_13_19.ExtendedCheck nodes 3 := by decide
def rotationDot_13_20 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_13_20_checked : rotationDot_13_20.ExtendedCheck nodes 3 := by decide
def rotationDot_13_21 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2206][i]?.getD 0
  accumulator := fun i => #[11,11,11,2206][i]?.getD 0
theorem rotationDot_13_21_checked : rotationDot_13_21.ExtendedCheck nodes 3 := by decide
def rotationDot_13_22 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,2206][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2299][i]?.getD 0
theorem rotationDot_13_22_checked : rotationDot_13_22.ExtendedCheck nodes 3 := by decide
def rotationDot_13_23 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_13_23_checked : rotationDot_13_23.ExtendedCheck nodes 3 := by decide
def rotationDot_13_24 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2209][i]?.getD 0
  accumulator := fun i => #[11,11,11,2209][i]?.getD 0
theorem rotationDot_13_24_checked : rotationDot_13_24.ExtendedCheck nodes 3 := by decide
def rotationDot_13_25 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,2206][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2299][i]?.getD 0
theorem rotationDot_13_25_checked : rotationDot_13_25.ExtendedCheck nodes 3 := by decide
def rotationDot_13_26 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_13_26_checked : rotationDot_13_26.ExtendedCheck nodes 3 := by decide
def rotationDot_13_27 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2209][i]?.getD 0
  accumulator := fun i => #[11,11,11,2209][i]?.getD 0
theorem rotationDot_13_27_checked : rotationDot_13_27.ExtendedCheck nodes 3 := by decide
def rotationDot_13_28 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,2227][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2295][i]?.getD 0
theorem rotationDot_13_28_checked : rotationDot_13_28.ExtendedCheck nodes 3 := by decide
def rotationDot_13_29 : DotRecipe where
  left := fun i => #[12,11,13][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_13_29_checked : rotationDot_13_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow13 : Array DotRecipe := #[rotationDot_13_0,rotationDot_13_1,rotationDot_13_2,rotationDot_13_3,rotationDot_13_4,rotationDot_13_5,rotationDot_13_6,rotationDot_13_7,rotationDot_13_8,rotationDot_13_9,rotationDot_13_10,rotationDot_13_11,rotationDot_13_12,rotationDot_13_13,rotationDot_13_14,rotationDot_13_15,rotationDot_13_16,rotationDot_13_17,rotationDot_13_18,rotationDot_13_19,rotationDot_13_20,rotationDot_13_21,rotationDot_13_22,rotationDot_13_23,rotationDot_13_24,rotationDot_13_25,rotationDot_13_26,rotationDot_13_27,rotationDot_13_28,rotationDot_13_29]
theorem rotationDotsRow13_checked (j : Fin 30) :
    (rotationDotsRow13[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_13_0_checked
  · exact rotationDot_13_1_checked
  · exact rotationDot_13_2_checked
  · exact rotationDot_13_3_checked
  · exact rotationDot_13_4_checked
  · exact rotationDot_13_5_checked
  · exact rotationDot_13_6_checked
  · exact rotationDot_13_7_checked
  · exact rotationDot_13_8_checked
  · exact rotationDot_13_9_checked
  · exact rotationDot_13_10_checked
  · exact rotationDot_13_11_checked
  · exact rotationDot_13_12_checked
  · exact rotationDot_13_13_checked
  · exact rotationDot_13_14_checked
  · exact rotationDot_13_15_checked
  · exact rotationDot_13_16_checked
  · exact rotationDot_13_17_checked
  · exact rotationDot_13_18_checked
  · exact rotationDot_13_19_checked
  · exact rotationDot_13_20_checked
  · exact rotationDot_13_21_checked
  · exact rotationDot_13_22_checked
  · exact rotationDot_13_23_checked
  · exact rotationDot_13_24_checked
  · exact rotationDot_13_25_checked
  · exact rotationDot_13_26_checked
  · exact rotationDot_13_27_checked
  · exact rotationDot_13_28_checked
  · exact rotationDot_13_29_checked
def rotationDot_14_0 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,345,11][i]?.getD 0
  accumulator := fun i => #[11,11,345,345][i]?.getD 0
theorem rotationDot_14_0_checked : rotationDot_14_0.ExtendedCheck nodes 3 := by decide
def rotationDot_14_1 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_1_checked : rotationDot_14_1.ExtendedCheck nodes 3 := by decide
def rotationDot_14_2 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_2_checked : rotationDot_14_2.ExtendedCheck nodes 3 := by decide
def rotationDot_14_3 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2309,11][i]?.getD 0
  accumulator := fun i => #[11,11,2309,2309][i]?.getD 0
theorem rotationDot_14_3_checked : rotationDot_14_3.ExtendedCheck nodes 3 := by decide
def rotationDot_14_4 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_4_checked : rotationDot_14_4.ExtendedCheck nodes 3 := by decide
def rotationDot_14_5 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_5_checked : rotationDot_14_5.ExtendedCheck nodes 3 := by decide
def rotationDot_14_6 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2311,11][i]?.getD 0
  accumulator := fun i => #[11,11,2311,2311][i]?.getD 0
theorem rotationDot_14_6_checked : rotationDot_14_6.ExtendedCheck nodes 3 := by decide
def rotationDot_14_7 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_7_checked : rotationDot_14_7.ExtendedCheck nodes 3 := by decide
def rotationDot_14_8 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2313,11][i]?.getD 0
  accumulator := fun i => #[11,11,2313,2313][i]?.getD 0
theorem rotationDot_14_8_checked : rotationDot_14_8.ExtendedCheck nodes 3 := by decide
def rotationDot_14_9 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2311,11][i]?.getD 0
  accumulator := fun i => #[11,11,2311,2311][i]?.getD 0
theorem rotationDot_14_9_checked : rotationDot_14_9.ExtendedCheck nodes 3 := by decide
def rotationDot_14_10 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_10_checked : rotationDot_14_10.ExtendedCheck nodes 3 := by decide
def rotationDot_14_11 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_11_checked : rotationDot_14_11.ExtendedCheck nodes 3 := by decide
def rotationDot_14_12 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2311,11][i]?.getD 0
  accumulator := fun i => #[11,11,2311,2311][i]?.getD 0
theorem rotationDot_14_12_checked : rotationDot_14_12.ExtendedCheck nodes 3 := by decide
def rotationDot_14_13 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_13_checked : rotationDot_14_13.ExtendedCheck nodes 3 := by decide
def rotationDot_14_14 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,346,11][i]?.getD 0
  accumulator := fun i => #[11,11,346,346][i]?.getD 0
theorem rotationDot_14_14_checked : rotationDot_14_14.ExtendedCheck nodes 3 := by decide
def rotationDot_14_15 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2311,11][i]?.getD 0
  accumulator := fun i => #[11,11,2311,2311][i]?.getD 0
theorem rotationDot_14_15_checked : rotationDot_14_15.ExtendedCheck nodes 3 := by decide
def rotationDot_14_16 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_16_checked : rotationDot_14_16.ExtendedCheck nodes 3 := by decide
def rotationDot_14_17 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_17_checked : rotationDot_14_17.ExtendedCheck nodes 3 := by decide
def rotationDot_14_18 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2319,11][i]?.getD 0
  accumulator := fun i => #[11,11,2319,2319][i]?.getD 0
theorem rotationDot_14_18_checked : rotationDot_14_18.ExtendedCheck nodes 3 := by decide
def rotationDot_14_19 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_19_checked : rotationDot_14_19.ExtendedCheck nodes 3 := by decide
def rotationDot_14_20 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2321,11][i]?.getD 0
  accumulator := fun i => #[11,11,2321,2321][i]?.getD 0
theorem rotationDot_14_20_checked : rotationDot_14_20.ExtendedCheck nodes 3 := by decide
def rotationDot_14_21 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2319,11][i]?.getD 0
  accumulator := fun i => #[11,11,2319,2319][i]?.getD 0
theorem rotationDot_14_21_checked : rotationDot_14_21.ExtendedCheck nodes 3 := by decide
def rotationDot_14_22 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_22_checked : rotationDot_14_22.ExtendedCheck nodes 3 := by decide
def rotationDot_14_23 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2324,11][i]?.getD 0
  accumulator := fun i => #[11,11,2324,2324][i]?.getD 0
theorem rotationDot_14_23_checked : rotationDot_14_23.ExtendedCheck nodes 3 := by decide
def rotationDot_14_24 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2319,11][i]?.getD 0
  accumulator := fun i => #[11,11,2319,2319][i]?.getD 0
theorem rotationDot_14_24_checked : rotationDot_14_24.ExtendedCheck nodes 3 := by decide
def rotationDot_14_25 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_25_checked : rotationDot_14_25.ExtendedCheck nodes 3 := by decide
def rotationDot_14_26 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2324,11][i]?.getD 0
  accumulator := fun i => #[11,11,2324,2324][i]?.getD 0
theorem rotationDot_14_26_checked : rotationDot_14_26.ExtendedCheck nodes 3 := by decide
def rotationDot_14_27 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2319,11][i]?.getD 0
  accumulator := fun i => #[11,11,2319,2319][i]?.getD 0
theorem rotationDot_14_27_checked : rotationDot_14_27.ExtendedCheck nodes 3 := by decide
def rotationDot_14_28 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_14_28_checked : rotationDot_14_28.ExtendedCheck nodes 3 := by decide
def rotationDot_14_29 : DotRecipe where
  left := fun i => #[11,345,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2321,11][i]?.getD 0
  accumulator := fun i => #[11,11,2321,2321][i]?.getD 0
theorem rotationDot_14_29_checked : rotationDot_14_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow14 : Array DotRecipe := #[rotationDot_14_0,rotationDot_14_1,rotationDot_14_2,rotationDot_14_3,rotationDot_14_4,rotationDot_14_5,rotationDot_14_6,rotationDot_14_7,rotationDot_14_8,rotationDot_14_9,rotationDot_14_10,rotationDot_14_11,rotationDot_14_12,rotationDot_14_13,rotationDot_14_14,rotationDot_14_15,rotationDot_14_16,rotationDot_14_17,rotationDot_14_18,rotationDot_14_19,rotationDot_14_20,rotationDot_14_21,rotationDot_14_22,rotationDot_14_23,rotationDot_14_24,rotationDot_14_25,rotationDot_14_26,rotationDot_14_27,rotationDot_14_28,rotationDot_14_29]
theorem rotationDotsRow14_checked (j : Fin 30) :
    (rotationDotsRow14[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_14_0_checked
  · exact rotationDot_14_1_checked
  · exact rotationDot_14_2_checked
  · exact rotationDot_14_3_checked
  · exact rotationDot_14_4_checked
  · exact rotationDot_14_5_checked
  · exact rotationDot_14_6_checked
  · exact rotationDot_14_7_checked
  · exact rotationDot_14_8_checked
  · exact rotationDot_14_9_checked
  · exact rotationDot_14_10_checked
  · exact rotationDot_14_11_checked
  · exact rotationDot_14_12_checked
  · exact rotationDot_14_13_checked
  · exact rotationDot_14_14_checked
  · exact rotationDot_14_15_checked
  · exact rotationDot_14_16_checked
  · exact rotationDot_14_17_checked
  · exact rotationDot_14_18_checked
  · exact rotationDot_14_19_checked
  · exact rotationDot_14_20_checked
  · exact rotationDot_14_21_checked
  · exact rotationDot_14_22_checked
  · exact rotationDot_14_23_checked
  · exact rotationDot_14_24_checked
  · exact rotationDot_14_25_checked
  · exact rotationDot_14_26_checked
  · exact rotationDot_14_27_checked
  · exact rotationDot_14_28_checked
  · exact rotationDot_14_29_checked
def rotationDot_15_0 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,0,11][i]?.getD 0
  accumulator := fun i => #[11,11,0,0][i]?.getD 0
theorem rotationDot_15_0_checked : rotationDot_15_0.ExtendedCheck nodes 3 := by decide
def rotationDot_15_1 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_1_checked : rotationDot_15_1.ExtendedCheck nodes 3 := by decide
def rotationDot_15_2 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_2_checked : rotationDot_15_2.ExtendedCheck nodes 3 := by decide
def rotationDot_15_3 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2135,11][i]?.getD 0
  accumulator := fun i => #[11,11,2135,2135][i]?.getD 0
theorem rotationDot_15_3_checked : rotationDot_15_3.ExtendedCheck nodes 3 := by decide
def rotationDot_15_4 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_4_checked : rotationDot_15_4.ExtendedCheck nodes 3 := by decide
def rotationDot_15_5 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_5_checked : rotationDot_15_5.ExtendedCheck nodes 3 := by decide
def rotationDot_15_6 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_15_6_checked : rotationDot_15_6.ExtendedCheck nodes 3 := by decide
def rotationDot_15_7 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2331][i]?.getD 0
  accumulator := fun i => #[11,11,11,2331][i]?.getD 0
theorem rotationDot_15_7_checked : rotationDot_15_7.ExtendedCheck nodes 3 := by decide
def rotationDot_15_8 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2138,11][i]?.getD 0
  accumulator := fun i => #[11,11,2138,2138][i]?.getD 0
theorem rotationDot_15_8_checked : rotationDot_15_8.ExtendedCheck nodes 3 := by decide
def rotationDot_15_9 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,1,2313][i]?.getD 0
  accumulator := fun i => #[11,11,1,2334][i]?.getD 0
theorem rotationDot_15_9_checked : rotationDot_15_9.ExtendedCheck nodes 3 := by decide
def rotationDot_15_10 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_10_checked : rotationDot_15_10.ExtendedCheck nodes 3 := by decide
def rotationDot_15_11 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_11_checked : rotationDot_15_11.ExtendedCheck nodes 3 := by decide
def rotationDot_15_12 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,1,11][i]?.getD 0
  accumulator := fun i => #[11,11,1,1][i]?.getD 0
theorem rotationDot_15_12_checked : rotationDot_15_12.ExtendedCheck nodes 3 := by decide
def rotationDot_15_13 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,2313][i]?.getD 0
  accumulator := fun i => #[11,11,11,2313][i]?.getD 0
theorem rotationDot_15_13_checked : rotationDot_15_13.ExtendedCheck nodes 3 := by decide
def rotationDot_15_14 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2142,11][i]?.getD 0
  accumulator := fun i => #[11,11,2142,2142][i]?.getD 0
theorem rotationDot_15_14_checked : rotationDot_15_14.ExtendedCheck nodes 3 := by decide
def rotationDot_15_15 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,1,346][i]?.getD 0
  accumulator := fun i => #[11,11,1,2338][i]?.getD 0
theorem rotationDot_15_15_checked : rotationDot_15_15.ExtendedCheck nodes 3 := by decide
def rotationDot_15_16 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_16_checked : rotationDot_15_16.ExtendedCheck nodes 3 := by decide
def rotationDot_15_17 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_15_17_checked : rotationDot_15_17.ExtendedCheck nodes 3 := by decide
def rotationDot_15_18 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,2321][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2340][i]?.getD 0
theorem rotationDot_15_18_checked : rotationDot_15_18.ExtendedCheck nodes 3 := by decide
def rotationDot_15_19 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2342][i]?.getD 0
  accumulator := fun i => #[11,11,11,2342][i]?.getD 0
theorem rotationDot_15_19_checked : rotationDot_15_19.ExtendedCheck nodes 3 := by decide
def rotationDot_15_20 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_15_20_checked : rotationDot_15_20.ExtendedCheck nodes 3 := by decide
def rotationDot_15_21 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2145,2321][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2340][i]?.getD 0
theorem rotationDot_15_21_checked : rotationDot_15_21.ExtendedCheck nodes 3 := by decide
def rotationDot_15_22 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2321][i]?.getD 0
  accumulator := fun i => #[11,11,11,2321][i]?.getD 0
theorem rotationDot_15_22_checked : rotationDot_15_22.ExtendedCheck nodes 3 := by decide
def rotationDot_15_23 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_15_23_checked : rotationDot_15_23.ExtendedCheck nodes 3 := by decide
def rotationDot_15_24 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,2324][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2348][i]?.getD 0
theorem rotationDot_15_24_checked : rotationDot_15_24.ExtendedCheck nodes 3 := by decide
def rotationDot_15_25 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2321][i]?.getD 0
  accumulator := fun i => #[11,11,11,2321][i]?.getD 0
theorem rotationDot_15_25_checked : rotationDot_15_25.ExtendedCheck nodes 3 := by decide
def rotationDot_15_26 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2150,11][i]?.getD 0
  accumulator := fun i => #[11,11,2150,2150][i]?.getD 0
theorem rotationDot_15_26_checked : rotationDot_15_26.ExtendedCheck nodes 3 := by decide
def rotationDot_15_27 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2145,2324][i]?.getD 0
  accumulator := fun i => #[11,11,2145,2348][i]?.getD 0
theorem rotationDot_15_27_checked : rotationDot_15_27.ExtendedCheck nodes 3 := by decide
def rotationDot_15_28 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2342][i]?.getD 0
  accumulator := fun i => #[11,11,11,2342][i]?.getD 0
theorem rotationDot_15_28_checked : rotationDot_15_28.ExtendedCheck nodes 3 := by decide
def rotationDot_15_29 : DotRecipe where
  left := fun i => #[11,0,345][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2147,11][i]?.getD 0
  accumulator := fun i => #[11,11,2147,2147][i]?.getD 0
theorem rotationDot_15_29_checked : rotationDot_15_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow15 : Array DotRecipe := #[rotationDot_15_0,rotationDot_15_1,rotationDot_15_2,rotationDot_15_3,rotationDot_15_4,rotationDot_15_5,rotationDot_15_6,rotationDot_15_7,rotationDot_15_8,rotationDot_15_9,rotationDot_15_10,rotationDot_15_11,rotationDot_15_12,rotationDot_15_13,rotationDot_15_14,rotationDot_15_15,rotationDot_15_16,rotationDot_15_17,rotationDot_15_18,rotationDot_15_19,rotationDot_15_20,rotationDot_15_21,rotationDot_15_22,rotationDot_15_23,rotationDot_15_24,rotationDot_15_25,rotationDot_15_26,rotationDot_15_27,rotationDot_15_28,rotationDot_15_29]
theorem rotationDotsRow15_checked (j : Fin 30) :
    (rotationDotsRow15[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_15_0_checked
  · exact rotationDot_15_1_checked
  · exact rotationDot_15_2_checked
  · exact rotationDot_15_3_checked
  · exact rotationDot_15_4_checked
  · exact rotationDot_15_5_checked
  · exact rotationDot_15_6_checked
  · exact rotationDot_15_7_checked
  · exact rotationDot_15_8_checked
  · exact rotationDot_15_9_checked
  · exact rotationDot_15_10_checked
  · exact rotationDot_15_11_checked
  · exact rotationDot_15_12_checked
  · exact rotationDot_15_13_checked
  · exact rotationDot_15_14_checked
  · exact rotationDot_15_15_checked
  · exact rotationDot_15_16_checked
  · exact rotationDot_15_17_checked
  · exact rotationDot_15_18_checked
  · exact rotationDot_15_19_checked
  · exact rotationDot_15_20_checked
  · exact rotationDot_15_21_checked
  · exact rotationDot_15_22_checked
  · exact rotationDot_15_23_checked
  · exact rotationDot_15_24_checked
  · exact rotationDot_15_25_checked
  · exact rotationDot_15_26_checked
  · exact rotationDot_15_27_checked
  · exact rotationDot_15_28_checked
  · exact rotationDot_15_29_checked
def rotationDot_16_0 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_0_checked : rotationDot_16_0.ExtendedCheck nodes 3 := by decide
def rotationDot_16_1 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2156,11,11][i]?.getD 0
  accumulator := fun i => #[11,2156,2156,2156][i]?.getD 0
theorem rotationDot_16_1_checked : rotationDot_16_1.ExtendedCheck nodes 3 := by decide
def rotationDot_16_2 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_2_checked : rotationDot_16_2.ExtendedCheck nodes 3 := by decide
def rotationDot_16_3 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_3_checked : rotationDot_16_3.ExtendedCheck nodes 3 := by decide
def rotationDot_16_4 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[12,11,11][i]?.getD 0
  accumulator := fun i => #[11,12,12,12][i]?.getD 0
theorem rotationDot_16_4_checked : rotationDot_16_4.ExtendedCheck nodes 3 := by decide
def rotationDot_16_5 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_5_checked : rotationDot_16_5.ExtendedCheck nodes 3 := by decide
def rotationDot_16_6 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_6_checked : rotationDot_16_6.ExtendedCheck nodes 3 := by decide
def rotationDot_16_7 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_16_7_checked : rotationDot_16_7.ExtendedCheck nodes 3 := by decide
def rotationDot_16_8 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_8_checked : rotationDot_16_8.ExtendedCheck nodes 3 := by decide
def rotationDot_16_9 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_9_checked : rotationDot_16_9.ExtendedCheck nodes 3 := by decide
def rotationDot_16_10 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_16_10_checked : rotationDot_16_10.ExtendedCheck nodes 3 := by decide
def rotationDot_16_11 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2164,11,11][i]?.getD 0
  accumulator := fun i => #[11,2164,2164,2164][i]?.getD 0
theorem rotationDot_16_11_checked : rotationDot_16_11.ExtendedCheck nodes 3 := by decide
def rotationDot_16_12 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_12_checked : rotationDot_16_12.ExtendedCheck nodes 3 := by decide
def rotationDot_16_13 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_16_13_checked : rotationDot_16_13.ExtendedCheck nodes 3 := by decide
def rotationDot_16_14 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_14_checked : rotationDot_16_14.ExtendedCheck nodes 3 := by decide
def rotationDot_16_15 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_15_checked : rotationDot_16_15.ExtendedCheck nodes 3 := by decide
def rotationDot_16_16 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2158,11,11][i]?.getD 0
  accumulator := fun i => #[11,2158,2158,2158][i]?.getD 0
theorem rotationDot_16_16_checked : rotationDot_16_16.ExtendedCheck nodes 3 := by decide
def rotationDot_16_17 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2171,11,11][i]?.getD 0
  accumulator := fun i => #[11,2171,2171,2171][i]?.getD 0
theorem rotationDot_16_17_checked : rotationDot_16_17.ExtendedCheck nodes 3 := by decide
def rotationDot_16_18 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_18_checked : rotationDot_16_18.ExtendedCheck nodes 3 := by decide
def rotationDot_16_19 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_16_19_checked : rotationDot_16_19.ExtendedCheck nodes 3 := by decide
def rotationDot_16_20 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_16_20_checked : rotationDot_16_20.ExtendedCheck nodes 3 := by decide
def rotationDot_16_21 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_21_checked : rotationDot_16_21.ExtendedCheck nodes 3 := by decide
def rotationDot_16_22 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_16_22_checked : rotationDot_16_22.ExtendedCheck nodes 3 := by decide
def rotationDot_16_23 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2179,11,11][i]?.getD 0
  accumulator := fun i => #[11,2179,2179,2179][i]?.getD 0
theorem rotationDot_16_23_checked : rotationDot_16_23.ExtendedCheck nodes 3 := by decide
def rotationDot_16_24 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_24_checked : rotationDot_16_24.ExtendedCheck nodes 3 := by decide
def rotationDot_16_25 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_16_25_checked : rotationDot_16_25.ExtendedCheck nodes 3 := by decide
def rotationDot_16_26 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_16_26_checked : rotationDot_16_26.ExtendedCheck nodes 3 := by decide
def rotationDot_16_27 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_16_27_checked : rotationDot_16_27.ExtendedCheck nodes 3 := by decide
def rotationDot_16_28 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2175,11,11][i]?.getD 0
  accumulator := fun i => #[11,2175,2175,2175][i]?.getD 0
theorem rotationDot_16_28_checked : rotationDot_16_28.ExtendedCheck nodes 3 := by decide
def rotationDot_16_29 : DotRecipe where
  left := fun i => #[12,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2188,11,11][i]?.getD 0
  accumulator := fun i => #[11,2188,2188,2188][i]?.getD 0
theorem rotationDot_16_29_checked : rotationDot_16_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow16 : Array DotRecipe := #[rotationDot_16_0,rotationDot_16_1,rotationDot_16_2,rotationDot_16_3,rotationDot_16_4,rotationDot_16_5,rotationDot_16_6,rotationDot_16_7,rotationDot_16_8,rotationDot_16_9,rotationDot_16_10,rotationDot_16_11,rotationDot_16_12,rotationDot_16_13,rotationDot_16_14,rotationDot_16_15,rotationDot_16_16,rotationDot_16_17,rotationDot_16_18,rotationDot_16_19,rotationDot_16_20,rotationDot_16_21,rotationDot_16_22,rotationDot_16_23,rotationDot_16_24,rotationDot_16_25,rotationDot_16_26,rotationDot_16_27,rotationDot_16_28,rotationDot_16_29]
theorem rotationDotsRow16_checked (j : Fin 30) :
    (rotationDotsRow16[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_16_0_checked
  · exact rotationDot_16_1_checked
  · exact rotationDot_16_2_checked
  · exact rotationDot_16_3_checked
  · exact rotationDot_16_4_checked
  · exact rotationDot_16_5_checked
  · exact rotationDot_16_6_checked
  · exact rotationDot_16_7_checked
  · exact rotationDot_16_8_checked
  · exact rotationDot_16_9_checked
  · exact rotationDot_16_10_checked
  · exact rotationDot_16_11_checked
  · exact rotationDot_16_12_checked
  · exact rotationDot_16_13_checked
  · exact rotationDot_16_14_checked
  · exact rotationDot_16_15_checked
  · exact rotationDot_16_16_checked
  · exact rotationDot_16_17_checked
  · exact rotationDot_16_18_checked
  · exact rotationDot_16_19_checked
  · exact rotationDot_16_20_checked
  · exact rotationDot_16_21_checked
  · exact rotationDot_16_22_checked
  · exact rotationDot_16_23_checked
  · exact rotationDot_16_24_checked
  · exact rotationDot_16_25_checked
  · exact rotationDot_16_26_checked
  · exact rotationDot_16_27_checked
  · exact rotationDot_16_28_checked
  · exact rotationDot_16_29_checked
def rotationDot_17_0 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_0_checked : rotationDot_17_0.ExtendedCheck nodes 3 := by decide
def rotationDot_17_1 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2194,11,11][i]?.getD 0
  accumulator := fun i => #[11,2194,2194,2194][i]?.getD 0
theorem rotationDot_17_1_checked : rotationDot_17_1.ExtendedCheck nodes 3 := by decide
def rotationDot_17_2 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_2_checked : rotationDot_17_2.ExtendedCheck nodes 3 := by decide
def rotationDot_17_3 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_3_checked : rotationDot_17_3.ExtendedCheck nodes 3 := by decide
def rotationDot_17_4 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[13,11,11][i]?.getD 0
  accumulator := fun i => #[11,13,13,13][i]?.getD 0
theorem rotationDot_17_4_checked : rotationDot_17_4.ExtendedCheck nodes 3 := by decide
def rotationDot_17_5 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_5_checked : rotationDot_17_5.ExtendedCheck nodes 3 := by decide
def rotationDot_17_6 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_6_checked : rotationDot_17_6.ExtendedCheck nodes 3 := by decide
def rotationDot_17_7 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2204,11,11][i]?.getD 0
  accumulator := fun i => #[11,2204,2204,2204][i]?.getD 0
theorem rotationDot_17_7_checked : rotationDot_17_7.ExtendedCheck nodes 3 := by decide
def rotationDot_17_8 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_8_checked : rotationDot_17_8.ExtendedCheck nodes 3 := by decide
def rotationDot_17_9 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_9_checked : rotationDot_17_9.ExtendedCheck nodes 3 := by decide
def rotationDot_17_10 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2204,11,11][i]?.getD 0
  accumulator := fun i => #[11,2204,2204,2204][i]?.getD 0
theorem rotationDot_17_10_checked : rotationDot_17_10.ExtendedCheck nodes 3 := by decide
def rotationDot_17_11 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2216,11,11][i]?.getD 0
  accumulator := fun i => #[11,2216,2216,2216][i]?.getD 0
theorem rotationDot_17_11_checked : rotationDot_17_11.ExtendedCheck nodes 3 := by decide
def rotationDot_17_12 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_12_checked : rotationDot_17_12.ExtendedCheck nodes 3 := by decide
def rotationDot_17_13 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2204,11,11][i]?.getD 0
  accumulator := fun i => #[11,2204,2204,2204][i]?.getD 0
theorem rotationDot_17_13_checked : rotationDot_17_13.ExtendedCheck nodes 3 := by decide
def rotationDot_17_14 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_14_checked : rotationDot_17_14.ExtendedCheck nodes 3 := by decide
def rotationDot_17_15 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_15_checked : rotationDot_17_15.ExtendedCheck nodes 3 := by decide
def rotationDot_17_16 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2204,11,11][i]?.getD 0
  accumulator := fun i => #[11,2204,2204,2204][i]?.getD 0
theorem rotationDot_17_16_checked : rotationDot_17_16.ExtendedCheck nodes 3 := by decide
def rotationDot_17_17 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[113,11,11][i]?.getD 0
  accumulator := fun i => #[11,113,113,113][i]?.getD 0
theorem rotationDot_17_17_checked : rotationDot_17_17.ExtendedCheck nodes 3 := by decide
def rotationDot_17_18 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_18_checked : rotationDot_17_18.ExtendedCheck nodes 3 := by decide
def rotationDot_17_19 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2375,11,11][i]?.getD 0
  accumulator := fun i => #[11,2375,2375,2375][i]?.getD 0
theorem rotationDot_17_19_checked : rotationDot_17_19.ExtendedCheck nodes 3 := by decide
def rotationDot_17_20 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2227,11,11][i]?.getD 0
  accumulator := fun i => #[11,2227,2227,2227][i]?.getD 0
theorem rotationDot_17_20_checked : rotationDot_17_20.ExtendedCheck nodes 3 := by decide
def rotationDot_17_21 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_21_checked : rotationDot_17_21.ExtendedCheck nodes 3 := by decide
def rotationDot_17_22 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2375,11,11][i]?.getD 0
  accumulator := fun i => #[11,2375,2375,2375][i]?.getD 0
theorem rotationDot_17_22_checked : rotationDot_17_22.ExtendedCheck nodes 3 := by decide
def rotationDot_17_23 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2227,11,11][i]?.getD 0
  accumulator := fun i => #[11,2227,2227,2227][i]?.getD 0
theorem rotationDot_17_23_checked : rotationDot_17_23.ExtendedCheck nodes 3 := by decide
def rotationDot_17_24 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_24_checked : rotationDot_17_24.ExtendedCheck nodes 3 := by decide
def rotationDot_17_25 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2375,11,11][i]?.getD 0
  accumulator := fun i => #[11,2375,2375,2375][i]?.getD 0
theorem rotationDot_17_25_checked : rotationDot_17_25.ExtendedCheck nodes 3 := by decide
def rotationDot_17_26 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2206,11,11][i]?.getD 0
  accumulator := fun i => #[11,2206,2206,2206][i]?.getD 0
theorem rotationDot_17_26_checked : rotationDot_17_26.ExtendedCheck nodes 3 := by decide
def rotationDot_17_27 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_17_27_checked : rotationDot_17_27.ExtendedCheck nodes 3 := by decide
def rotationDot_17_28 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2375,11,11][i]?.getD 0
  accumulator := fun i => #[11,2375,2375,2375][i]?.getD 0
theorem rotationDot_17_28_checked : rotationDot_17_28.ExtendedCheck nodes 3 := by decide
def rotationDot_17_29 : DotRecipe where
  left := fun i => #[13,11,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2206,11,11][i]?.getD 0
  accumulator := fun i => #[11,2206,2206,2206][i]?.getD 0
theorem rotationDot_17_29_checked : rotationDot_17_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow17 : Array DotRecipe := #[rotationDot_17_0,rotationDot_17_1,rotationDot_17_2,rotationDot_17_3,rotationDot_17_4,rotationDot_17_5,rotationDot_17_6,rotationDot_17_7,rotationDot_17_8,rotationDot_17_9,rotationDot_17_10,rotationDot_17_11,rotationDot_17_12,rotationDot_17_13,rotationDot_17_14,rotationDot_17_15,rotationDot_17_16,rotationDot_17_17,rotationDot_17_18,rotationDot_17_19,rotationDot_17_20,rotationDot_17_21,rotationDot_17_22,rotationDot_17_23,rotationDot_17_24,rotationDot_17_25,rotationDot_17_26,rotationDot_17_27,rotationDot_17_28,rotationDot_17_29]
theorem rotationDotsRow17_checked (j : Fin 30) :
    (rotationDotsRow17[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_17_0_checked
  · exact rotationDot_17_1_checked
  · exact rotationDot_17_2_checked
  · exact rotationDot_17_3_checked
  · exact rotationDot_17_4_checked
  · exact rotationDot_17_5_checked
  · exact rotationDot_17_6_checked
  · exact rotationDot_17_7_checked
  · exact rotationDot_17_8_checked
  · exact rotationDot_17_9_checked
  · exact rotationDot_17_10_checked
  · exact rotationDot_17_11_checked
  · exact rotationDot_17_12_checked
  · exact rotationDot_17_13_checked
  · exact rotationDot_17_14_checked
  · exact rotationDot_17_15_checked
  · exact rotationDot_17_16_checked
  · exact rotationDot_17_17_checked
  · exact rotationDot_17_18_checked
  · exact rotationDot_17_19_checked
  · exact rotationDot_17_20_checked
  · exact rotationDot_17_21_checked
  · exact rotationDot_17_22_checked
  · exact rotationDot_17_23_checked
  · exact rotationDot_17_24_checked
  · exact rotationDot_17_25_checked
  · exact rotationDot_17_26_checked
  · exact rotationDot_17_27_checked
  · exact rotationDot_17_28_checked
  · exact rotationDot_17_29_checked
def rotationDot_18_0 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_18_0_checked : rotationDot_18_0.ExtendedCheck nodes 3 := by decide
def rotationDot_18_1 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_1_checked : rotationDot_18_1.ExtendedCheck nodes 3 := by decide
def rotationDot_18_2 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_2_checked : rotationDot_18_2.ExtendedCheck nodes 3 := by decide
def rotationDot_18_3 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2156,11][i]?.getD 0
  accumulator := fun i => #[11,11,2156,2156][i]?.getD 0
theorem rotationDot_18_3_checked : rotationDot_18_3.ExtendedCheck nodes 3 := by decide
def rotationDot_18_4 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_4_checked : rotationDot_18_4.ExtendedCheck nodes 3 := by decide
def rotationDot_18_5 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_5_checked : rotationDot_18_5.ExtendedCheck nodes 3 := by decide
def rotationDot_18_6 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_18_6_checked : rotationDot_18_6.ExtendedCheck nodes 3 := by decide
def rotationDot_18_7 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2387][i]?.getD 0
  accumulator := fun i => #[11,11,11,2387][i]?.getD 0
theorem rotationDot_18_7_checked : rotationDot_18_7.ExtendedCheck nodes 3 := by decide
def rotationDot_18_8 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2171,11][i]?.getD 0
  accumulator := fun i => #[11,11,2171,2171][i]?.getD 0
theorem rotationDot_18_8_checked : rotationDot_18_8.ExtendedCheck nodes 3 := by decide
def rotationDot_18_9 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2385,2390][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2391][i]?.getD 0
theorem rotationDot_18_9_checked : rotationDot_18_9.ExtendedCheck nodes 3 := by decide
def rotationDot_18_10 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_10_checked : rotationDot_18_10.ExtendedCheck nodes 3 := by decide
def rotationDot_18_11 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_11_checked : rotationDot_18_11.ExtendedCheck nodes 3 := by decide
def rotationDot_18_12 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_18_12_checked : rotationDot_18_12.ExtendedCheck nodes 3 := by decide
def rotationDot_18_13 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,2390][i]?.getD 0
  accumulator := fun i => #[11,11,11,2390][i]?.getD 0
theorem rotationDot_18_13_checked : rotationDot_18_13.ExtendedCheck nodes 3 := by decide
def rotationDot_18_14 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2395,11][i]?.getD 0
  accumulator := fun i => #[11,11,2395,2395][i]?.getD 0
theorem rotationDot_18_14_checked : rotationDot_18_14.ExtendedCheck nodes 3 := by decide
def rotationDot_18_15 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2385,2397][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2398][i]?.getD 0
theorem rotationDot_18_15_checked : rotationDot_18_15.ExtendedCheck nodes 3 := by decide
def rotationDot_18_16 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_16_checked : rotationDot_18_16.ExtendedCheck nodes 3 := by decide
def rotationDot_18_17 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_18_17_checked : rotationDot_18_17.ExtendedCheck nodes 3 := by decide
def rotationDot_18_18 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,710][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2400][i]?.getD 0
theorem rotationDot_18_18_checked : rotationDot_18_18.ExtendedCheck nodes 3 := by decide
def rotationDot_18_19 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2402][i]?.getD 0
  accumulator := fun i => #[11,11,11,2402][i]?.getD 0
theorem rotationDot_18_19_checked : rotationDot_18_19.ExtendedCheck nodes 3 := by decide
def rotationDot_18_20 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_18_20_checked : rotationDot_18_20.ExtendedCheck nodes 3 := by decide
def rotationDot_18_21 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,710][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2400][i]?.getD 0
theorem rotationDot_18_21_checked : rotationDot_18_21.ExtendedCheck nodes 3 := by decide
def rotationDot_18_22 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_18_22_checked : rotationDot_18_22.ExtendedCheck nodes 3 := by decide
def rotationDot_18_23 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_18_23_checked : rotationDot_18_23.ExtendedCheck nodes 3 := by decide
def rotationDot_18_24 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2409][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2410][i]?.getD 0
theorem rotationDot_18_24_checked : rotationDot_18_24.ExtendedCheck nodes 3 := by decide
def rotationDot_18_25 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_18_25_checked : rotationDot_18_25.ExtendedCheck nodes 3 := by decide
def rotationDot_18_26 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_18_26_checked : rotationDot_18_26.ExtendedCheck nodes 3 := by decide
def rotationDot_18_27 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2409][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2410][i]?.getD 0
theorem rotationDot_18_27_checked : rotationDot_18_27.ExtendedCheck nodes 3 := by decide
def rotationDot_18_28 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2402][i]?.getD 0
  accumulator := fun i => #[11,11,11,2402][i]?.getD 0
theorem rotationDot_18_28_checked : rotationDot_18_28.ExtendedCheck nodes 3 := by decide
def rotationDot_18_29 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_18_29_checked : rotationDot_18_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow18 : Array DotRecipe := #[rotationDot_18_0,rotationDot_18_1,rotationDot_18_2,rotationDot_18_3,rotationDot_18_4,rotationDot_18_5,rotationDot_18_6,rotationDot_18_7,rotationDot_18_8,rotationDot_18_9,rotationDot_18_10,rotationDot_18_11,rotationDot_18_12,rotationDot_18_13,rotationDot_18_14,rotationDot_18_15,rotationDot_18_16,rotationDot_18_17,rotationDot_18_18,rotationDot_18_19,rotationDot_18_20,rotationDot_18_21,rotationDot_18_22,rotationDot_18_23,rotationDot_18_24,rotationDot_18_25,rotationDot_18_26,rotationDot_18_27,rotationDot_18_28,rotationDot_18_29]
theorem rotationDotsRow18_checked (j : Fin 30) :
    (rotationDotsRow18[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_18_0_checked
  · exact rotationDot_18_1_checked
  · exact rotationDot_18_2_checked
  · exact rotationDot_18_3_checked
  · exact rotationDot_18_4_checked
  · exact rotationDot_18_5_checked
  · exact rotationDot_18_6_checked
  · exact rotationDot_18_7_checked
  · exact rotationDot_18_8_checked
  · exact rotationDot_18_9_checked
  · exact rotationDot_18_10_checked
  · exact rotationDot_18_11_checked
  · exact rotationDot_18_12_checked
  · exact rotationDot_18_13_checked
  · exact rotationDot_18_14_checked
  · exact rotationDot_18_15_checked
  · exact rotationDot_18_16_checked
  · exact rotationDot_18_17_checked
  · exact rotationDot_18_18_checked
  · exact rotationDot_18_19_checked
  · exact rotationDot_18_20_checked
  · exact rotationDot_18_21_checked
  · exact rotationDot_18_22_checked
  · exact rotationDot_18_23_checked
  · exact rotationDot_18_24_checked
  · exact rotationDot_18_25_checked
  · exact rotationDot_18_26_checked
  · exact rotationDot_18_27_checked
  · exact rotationDot_18_28_checked
  · exact rotationDot_18_29_checked
def rotationDot_19_0 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_0_checked : rotationDot_19_0.ExtendedCheck nodes 3 := by decide
def rotationDot_19_1 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2417,11,11][i]?.getD 0
  accumulator := fun i => #[11,2417,2417,2417][i]?.getD 0
theorem rotationDot_19_1_checked : rotationDot_19_1.ExtendedCheck nodes 3 := by decide
def rotationDot_19_2 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_2_checked : rotationDot_19_2.ExtendedCheck nodes 3 := by decide
def rotationDot_19_3 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_3_checked : rotationDot_19_3.ExtendedCheck nodes 3 := by decide
def rotationDot_19_4 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_19_4_checked : rotationDot_19_4.ExtendedCheck nodes 3 := by decide
def rotationDot_19_5 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_5_checked : rotationDot_19_5.ExtendedCheck nodes 3 := by decide
def rotationDot_19_6 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_6_checked : rotationDot_19_6.ExtendedCheck nodes 3 := by decide
def rotationDot_19_7 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2419,11,2420][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2421][i]?.getD 0
theorem rotationDot_19_7_checked : rotationDot_19_7.ExtendedCheck nodes 3 := by decide
def rotationDot_19_8 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_8_checked : rotationDot_19_8.ExtendedCheck nodes 3 := by decide
def rotationDot_19_9 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,2423][i]?.getD 0
  accumulator := fun i => #[11,11,11,2423][i]?.getD 0
theorem rotationDot_19_9_checked : rotationDot_19_9.ExtendedCheck nodes 3 := by decide
def rotationDot_19_10 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_19_10_checked : rotationDot_19_10.ExtendedCheck nodes 3 := by decide
def rotationDot_19_11 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2426,11,11][i]?.getD 0
  accumulator := fun i => #[11,2426,2426,2426][i]?.getD 0
theorem rotationDot_19_11_checked : rotationDot_19_11.ExtendedCheck nodes 3 := by decide
def rotationDot_19_12 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_12_checked : rotationDot_19_12.ExtendedCheck nodes 3 := by decide
def rotationDot_19_13 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2419,11,2423][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2428][i]?.getD 0
theorem rotationDot_19_13_checked : rotationDot_19_13.ExtendedCheck nodes 3 := by decide
def rotationDot_19_14 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_19_14_checked : rotationDot_19_14.ExtendedCheck nodes 3 := by decide
def rotationDot_19_15 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2430][i]?.getD 0
  accumulator := fun i => #[11,11,11,2430][i]?.getD 0
theorem rotationDot_19_15_checked : rotationDot_19_15.ExtendedCheck nodes 3 := by decide
def rotationDot_19_16 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_19_16_checked : rotationDot_19_16.ExtendedCheck nodes 3 := by decide
def rotationDot_19_17 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2433,11,11][i]?.getD 0
  accumulator := fun i => #[11,2433,2433,2433][i]?.getD 0
theorem rotationDot_19_17_checked : rotationDot_19_17.ExtendedCheck nodes 3 := by decide
def rotationDot_19_18 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2435][i]?.getD 0
  accumulator := fun i => #[11,11,11,2435][i]?.getD 0
theorem rotationDot_19_18_checked : rotationDot_19_18.ExtendedCheck nodes 3 := by decide
def rotationDot_19_19 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,403][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2438][i]?.getD 0
theorem rotationDot_19_19_checked : rotationDot_19_19.ExtendedCheck nodes 3 := by decide
def rotationDot_19_20 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_19_20_checked : rotationDot_19_20.ExtendedCheck nodes 3 := by decide
def rotationDot_19_21 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2435][i]?.getD 0
  accumulator := fun i => #[11,11,11,2435][i]?.getD 0
theorem rotationDot_19_21_checked : rotationDot_19_21.ExtendedCheck nodes 3 := by decide
def rotationDot_19_22 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,2435][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2443][i]?.getD 0
theorem rotationDot_19_22_checked : rotationDot_19_22.ExtendedCheck nodes 3 := by decide
def rotationDot_19_23 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_19_23_checked : rotationDot_19_23.ExtendedCheck nodes 3 := by decide
def rotationDot_19_24 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2446][i]?.getD 0
  accumulator := fun i => #[11,11,11,2446][i]?.getD 0
theorem rotationDot_19_24_checked : rotationDot_19_24.ExtendedCheck nodes 3 := by decide
def rotationDot_19_25 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,2435][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2443][i]?.getD 0
theorem rotationDot_19_25_checked : rotationDot_19_25.ExtendedCheck nodes 3 := by decide
def rotationDot_19_26 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_19_26_checked : rotationDot_19_26.ExtendedCheck nodes 3 := by decide
def rotationDot_19_27 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2446][i]?.getD 0
  accumulator := fun i => #[11,11,11,2446][i]?.getD 0
theorem rotationDot_19_27_checked : rotationDot_19_27.ExtendedCheck nodes 3 := by decide
def rotationDot_19_28 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,403][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2438][i]?.getD 0
theorem rotationDot_19_28_checked : rotationDot_19_28.ExtendedCheck nodes 3 := by decide
def rotationDot_19_29 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_19_29_checked : rotationDot_19_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow19 : Array DotRecipe := #[rotationDot_19_0,rotationDot_19_1,rotationDot_19_2,rotationDot_19_3,rotationDot_19_4,rotationDot_19_5,rotationDot_19_6,rotationDot_19_7,rotationDot_19_8,rotationDot_19_9,rotationDot_19_10,rotationDot_19_11,rotationDot_19_12,rotationDot_19_13,rotationDot_19_14,rotationDot_19_15,rotationDot_19_16,rotationDot_19_17,rotationDot_19_18,rotationDot_19_19,rotationDot_19_20,rotationDot_19_21,rotationDot_19_22,rotationDot_19_23,rotationDot_19_24,rotationDot_19_25,rotationDot_19_26,rotationDot_19_27,rotationDot_19_28,rotationDot_19_29]
theorem rotationDotsRow19_checked (j : Fin 30) :
    (rotationDotsRow19[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_19_0_checked
  · exact rotationDot_19_1_checked
  · exact rotationDot_19_2_checked
  · exact rotationDot_19_3_checked
  · exact rotationDot_19_4_checked
  · exact rotationDot_19_5_checked
  · exact rotationDot_19_6_checked
  · exact rotationDot_19_7_checked
  · exact rotationDot_19_8_checked
  · exact rotationDot_19_9_checked
  · exact rotationDot_19_10_checked
  · exact rotationDot_19_11_checked
  · exact rotationDot_19_12_checked
  · exact rotationDot_19_13_checked
  · exact rotationDot_19_14_checked
  · exact rotationDot_19_15_checked
  · exact rotationDot_19_16_checked
  · exact rotationDot_19_17_checked
  · exact rotationDot_19_18_checked
  · exact rotationDot_19_19_checked
  · exact rotationDot_19_20_checked
  · exact rotationDot_19_21_checked
  · exact rotationDot_19_22_checked
  · exact rotationDot_19_23_checked
  · exact rotationDot_19_24_checked
  · exact rotationDot_19_25_checked
  · exact rotationDot_19_26_checked
  · exact rotationDot_19_27_checked
  · exact rotationDot_19_28_checked
  · exact rotationDot_19_29_checked
def rotationDot_20_0 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,14,11][i]?.getD 0
  accumulator := fun i => #[11,11,14,14][i]?.getD 0
theorem rotationDot_20_0_checked : rotationDot_20_0.ExtendedCheck nodes 3 := by decide
def rotationDot_20_1 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2455,11,11][i]?.getD 0
  accumulator := fun i => #[11,2455,2455,2455][i]?.getD 0
theorem rotationDot_20_1_checked : rotationDot_20_1.ExtendedCheck nodes 3 := by decide
def rotationDot_20_2 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_20_2_checked : rotationDot_20_2.ExtendedCheck nodes 3 := by decide
def rotationDot_20_3 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2457,11][i]?.getD 0
  accumulator := fun i => #[11,11,2457,2457][i]?.getD 0
theorem rotationDot_20_3_checked : rotationDot_20_3.ExtendedCheck nodes 3 := by decide
def rotationDot_20_4 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[10,11,11][i]?.getD 0
  accumulator := fun i => #[11,10,10,10][i]?.getD 0
theorem rotationDot_20_4_checked : rotationDot_20_4.ExtendedCheck nodes 3 := by decide
def rotationDot_20_5 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_20_5_checked : rotationDot_20_5.ExtendedCheck nodes 3 := by decide
def rotationDot_20_6 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_20_6_checked : rotationDot_20_6.ExtendedCheck nodes 3 := by decide
def rotationDot_20_7 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_20_7_checked : rotationDot_20_7.ExtendedCheck nodes 3 := by decide
def rotationDot_20_8 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2390,11][i]?.getD 0
  accumulator := fun i => #[11,11,2390,2390][i]?.getD 0
theorem rotationDot_20_8_checked : rotationDot_20_8.ExtendedCheck nodes 3 := by decide
def rotationDot_20_9 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_20_9_checked : rotationDot_20_9.ExtendedCheck nodes 3 := by decide
def rotationDot_20_10 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_20_10_checked : rotationDot_20_10.ExtendedCheck nodes 3 := by decide
def rotationDot_20_11 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2420,11,11][i]?.getD 0
  accumulator := fun i => #[11,2420,2420,2420][i]?.getD 0
theorem rotationDot_20_11_checked : rotationDot_20_11.ExtendedCheck nodes 3 := by decide
def rotationDot_20_12 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_20_12_checked : rotationDot_20_12.ExtendedCheck nodes 3 := by decide
def rotationDot_20_13 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_20_13_checked : rotationDot_20_13.ExtendedCheck nodes 3 := by decide
def rotationDot_20_14 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2397,11][i]?.getD 0
  accumulator := fun i => #[11,11,2397,2397][i]?.getD 0
theorem rotationDot_20_14_checked : rotationDot_20_14.ExtendedCheck nodes 3 := by decide
def rotationDot_20_15 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_20_15_checked : rotationDot_20_15.ExtendedCheck nodes 3 := by decide
def rotationDot_20_16 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_20_16_checked : rotationDot_20_16.ExtendedCheck nodes 3 := by decide
def rotationDot_20_17 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2423,11,11][i]?.getD 0
  accumulator := fun i => #[11,2423,2423,2423][i]?.getD 0
theorem rotationDot_20_17_checked : rotationDot_20_17.ExtendedCheck nodes 3 := by decide
def rotationDot_20_18 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_20_18_checked : rotationDot_20_18.ExtendedCheck nodes 3 := by decide
def rotationDot_20_19 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_20_19_checked : rotationDot_20_19.ExtendedCheck nodes 3 := by decide
def rotationDot_20_20 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[403,710,11][i]?.getD 0
  accumulator := fun i => #[11,403,1521,1521][i]?.getD 0
theorem rotationDot_20_20_checked : rotationDot_20_20.ExtendedCheck nodes 3 := by decide
def rotationDot_20_21 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_20_21_checked : rotationDot_20_21.ExtendedCheck nodes 3 := by decide
def rotationDot_20_22 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_20_22_checked : rotationDot_20_22.ExtendedCheck nodes 3 := by decide
def rotationDot_20_23 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[403,2409,11][i]?.getD 0
  accumulator := fun i => #[11,403,2481,2481][i]?.getD 0
theorem rotationDot_20_23_checked : rotationDot_20_23.ExtendedCheck nodes 3 := by decide
def rotationDot_20_24 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_20_24_checked : rotationDot_20_24.ExtendedCheck nodes 3 := by decide
def rotationDot_20_25 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_20_25_checked : rotationDot_20_25.ExtendedCheck nodes 3 := by decide
def rotationDot_20_26 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2435,2409,11][i]?.getD 0
  accumulator := fun i => #[11,2435,2485,2485][i]?.getD 0
theorem rotationDot_20_26_checked : rotationDot_20_26.ExtendedCheck nodes 3 := by decide
def rotationDot_20_27 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_20_27_checked : rotationDot_20_27.ExtendedCheck nodes 3 := by decide
def rotationDot_20_28 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_20_28_checked : rotationDot_20_28.ExtendedCheck nodes 3 := by decide
def rotationDot_20_29 : DotRecipe where
  left := fun i => #[10,14,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2435,710,11][i]?.getD 0
  accumulator := fun i => #[11,2435,2489,2489][i]?.getD 0
theorem rotationDot_20_29_checked : rotationDot_20_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow20 : Array DotRecipe := #[rotationDot_20_0,rotationDot_20_1,rotationDot_20_2,rotationDot_20_3,rotationDot_20_4,rotationDot_20_5,rotationDot_20_6,rotationDot_20_7,rotationDot_20_8,rotationDot_20_9,rotationDot_20_10,rotationDot_20_11,rotationDot_20_12,rotationDot_20_13,rotationDot_20_14,rotationDot_20_15,rotationDot_20_16,rotationDot_20_17,rotationDot_20_18,rotationDot_20_19,rotationDot_20_20,rotationDot_20_21,rotationDot_20_22,rotationDot_20_23,rotationDot_20_24,rotationDot_20_25,rotationDot_20_26,rotationDot_20_27,rotationDot_20_28,rotationDot_20_29]
theorem rotationDotsRow20_checked (j : Fin 30) :
    (rotationDotsRow20[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_20_0_checked
  · exact rotationDot_20_1_checked
  · exact rotationDot_20_2_checked
  · exact rotationDot_20_3_checked
  · exact rotationDot_20_4_checked
  · exact rotationDot_20_5_checked
  · exact rotationDot_20_6_checked
  · exact rotationDot_20_7_checked
  · exact rotationDot_20_8_checked
  · exact rotationDot_20_9_checked
  · exact rotationDot_20_10_checked
  · exact rotationDot_20_11_checked
  · exact rotationDot_20_12_checked
  · exact rotationDot_20_13_checked
  · exact rotationDot_20_14_checked
  · exact rotationDot_20_15_checked
  · exact rotationDot_20_16_checked
  · exact rotationDot_20_17_checked
  · exact rotationDot_20_18_checked
  · exact rotationDot_20_19_checked
  · exact rotationDot_20_20_checked
  · exact rotationDot_20_21_checked
  · exact rotationDot_20_22_checked
  · exact rotationDot_20_23_checked
  · exact rotationDot_20_24_checked
  · exact rotationDot_20_25_checked
  · exact rotationDot_20_26_checked
  · exact rotationDot_20_27_checked
  · exact rotationDot_20_28_checked
  · exact rotationDot_20_29_checked
def rotationDot_21_0 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_21_0_checked : rotationDot_21_0.ExtendedCheck nodes 3 := by decide
def rotationDot_21_1 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_1_checked : rotationDot_21_1.ExtendedCheck nodes 3 := by decide
def rotationDot_21_2 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_2_checked : rotationDot_21_2.ExtendedCheck nodes 3 := by decide
def rotationDot_21_3 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2156,11][i]?.getD 0
  accumulator := fun i => #[11,11,2156,2156][i]?.getD 0
theorem rotationDot_21_3_checked : rotationDot_21_3.ExtendedCheck nodes 3 := by decide
def rotationDot_21_4 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_4_checked : rotationDot_21_4.ExtendedCheck nodes 3 := by decide
def rotationDot_21_5 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_5_checked : rotationDot_21_5.ExtendedCheck nodes 3 := by decide
def rotationDot_21_6 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_21_6_checked : rotationDot_21_6.ExtendedCheck nodes 3 := by decide
def rotationDot_21_7 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2387][i]?.getD 0
  accumulator := fun i => #[11,11,11,2387][i]?.getD 0
theorem rotationDot_21_7_checked : rotationDot_21_7.ExtendedCheck nodes 3 := by decide
def rotationDot_21_8 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2171,11][i]?.getD 0
  accumulator := fun i => #[11,11,2171,2171][i]?.getD 0
theorem rotationDot_21_8_checked : rotationDot_21_8.ExtendedCheck nodes 3 := by decide
def rotationDot_21_9 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2385,2390][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2391][i]?.getD 0
theorem rotationDot_21_9_checked : rotationDot_21_9.ExtendedCheck nodes 3 := by decide
def rotationDot_21_10 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_10_checked : rotationDot_21_10.ExtendedCheck nodes 3 := by decide
def rotationDot_21_11 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_11_checked : rotationDot_21_11.ExtendedCheck nodes 3 := by decide
def rotationDot_21_12 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_21_12_checked : rotationDot_21_12.ExtendedCheck nodes 3 := by decide
def rotationDot_21_13 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,2390][i]?.getD 0
  accumulator := fun i => #[11,11,11,2390][i]?.getD 0
theorem rotationDot_21_13_checked : rotationDot_21_13.ExtendedCheck nodes 3 := by decide
def rotationDot_21_14 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2395,11][i]?.getD 0
  accumulator := fun i => #[11,11,2395,2395][i]?.getD 0
theorem rotationDot_21_14_checked : rotationDot_21_14.ExtendedCheck nodes 3 := by decide
def rotationDot_21_15 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2385,2397][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2398][i]?.getD 0
theorem rotationDot_21_15_checked : rotationDot_21_15.ExtendedCheck nodes 3 := by decide
def rotationDot_21_16 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_16_checked : rotationDot_21_16.ExtendedCheck nodes 3 := by decide
def rotationDot_21_17 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_21_17_checked : rotationDot_21_17.ExtendedCheck nodes 3 := by decide
def rotationDot_21_18 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,710][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2400][i]?.getD 0
theorem rotationDot_21_18_checked : rotationDot_21_18.ExtendedCheck nodes 3 := by decide
def rotationDot_21_19 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2402][i]?.getD 0
  accumulator := fun i => #[11,11,11,2402][i]?.getD 0
theorem rotationDot_21_19_checked : rotationDot_21_19.ExtendedCheck nodes 3 := by decide
def rotationDot_21_20 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_21_20_checked : rotationDot_21_20.ExtendedCheck nodes 3 := by decide
def rotationDot_21_21 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,710][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2400][i]?.getD 0
theorem rotationDot_21_21_checked : rotationDot_21_21.ExtendedCheck nodes 3 := by decide
def rotationDot_21_22 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_21_22_checked : rotationDot_21_22.ExtendedCheck nodes 3 := by decide
def rotationDot_21_23 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_21_23_checked : rotationDot_21_23.ExtendedCheck nodes 3 := by decide
def rotationDot_21_24 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2409][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2410][i]?.getD 0
theorem rotationDot_21_24_checked : rotationDot_21_24.ExtendedCheck nodes 3 := by decide
def rotationDot_21_25 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_21_25_checked : rotationDot_21_25.ExtendedCheck nodes 3 := by decide
def rotationDot_21_26 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_21_26_checked : rotationDot_21_26.ExtendedCheck nodes 3 := by decide
def rotationDot_21_27 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2409][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2410][i]?.getD 0
theorem rotationDot_21_27_checked : rotationDot_21_27.ExtendedCheck nodes 3 := by decide
def rotationDot_21_28 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2402][i]?.getD 0
  accumulator := fun i => #[11,11,11,2402][i]?.getD 0
theorem rotationDot_21_28_checked : rotationDot_21_28.ExtendedCheck nodes 3 := by decide
def rotationDot_21_29 : DotRecipe where
  left := fun i => #[11,12,14][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_21_29_checked : rotationDot_21_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow21 : Array DotRecipe := #[rotationDot_21_0,rotationDot_21_1,rotationDot_21_2,rotationDot_21_3,rotationDot_21_4,rotationDot_21_5,rotationDot_21_6,rotationDot_21_7,rotationDot_21_8,rotationDot_21_9,rotationDot_21_10,rotationDot_21_11,rotationDot_21_12,rotationDot_21_13,rotationDot_21_14,rotationDot_21_15,rotationDot_21_16,rotationDot_21_17,rotationDot_21_18,rotationDot_21_19,rotationDot_21_20,rotationDot_21_21,rotationDot_21_22,rotationDot_21_23,rotationDot_21_24,rotationDot_21_25,rotationDot_21_26,rotationDot_21_27,rotationDot_21_28,rotationDot_21_29]
theorem rotationDotsRow21_checked (j : Fin 30) :
    (rotationDotsRow21[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_21_0_checked
  · exact rotationDot_21_1_checked
  · exact rotationDot_21_2_checked
  · exact rotationDot_21_3_checked
  · exact rotationDot_21_4_checked
  · exact rotationDot_21_5_checked
  · exact rotationDot_21_6_checked
  · exact rotationDot_21_7_checked
  · exact rotationDot_21_8_checked
  · exact rotationDot_21_9_checked
  · exact rotationDot_21_10_checked
  · exact rotationDot_21_11_checked
  · exact rotationDot_21_12_checked
  · exact rotationDot_21_13_checked
  · exact rotationDot_21_14_checked
  · exact rotationDot_21_15_checked
  · exact rotationDot_21_16_checked
  · exact rotationDot_21_17_checked
  · exact rotationDot_21_18_checked
  · exact rotationDot_21_19_checked
  · exact rotationDot_21_20_checked
  · exact rotationDot_21_21_checked
  · exact rotationDot_21_22_checked
  · exact rotationDot_21_23_checked
  · exact rotationDot_21_24_checked
  · exact rotationDot_21_25_checked
  · exact rotationDot_21_26_checked
  · exact rotationDot_21_27_checked
  · exact rotationDot_21_28_checked
  · exact rotationDot_21_29_checked
def rotationDot_22_0 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_0_checked : rotationDot_22_0.ExtendedCheck nodes 3 := by decide
def rotationDot_22_1 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2417,11,11][i]?.getD 0
  accumulator := fun i => #[11,2417,2417,2417][i]?.getD 0
theorem rotationDot_22_1_checked : rotationDot_22_1.ExtendedCheck nodes 3 := by decide
def rotationDot_22_2 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_2_checked : rotationDot_22_2.ExtendedCheck nodes 3 := by decide
def rotationDot_22_3 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_3_checked : rotationDot_22_3.ExtendedCheck nodes 3 := by decide
def rotationDot_22_4 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_22_4_checked : rotationDot_22_4.ExtendedCheck nodes 3 := by decide
def rotationDot_22_5 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_5_checked : rotationDot_22_5.ExtendedCheck nodes 3 := by decide
def rotationDot_22_6 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_6_checked : rotationDot_22_6.ExtendedCheck nodes 3 := by decide
def rotationDot_22_7 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2419,11,2387][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2512][i]?.getD 0
theorem rotationDot_22_7_checked : rotationDot_22_7.ExtendedCheck nodes 3 := by decide
def rotationDot_22_8 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_8_checked : rotationDot_22_8.ExtendedCheck nodes 3 := by decide
def rotationDot_22_9 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,2390][i]?.getD 0
  accumulator := fun i => #[11,11,11,2390][i]?.getD 0
theorem rotationDot_22_9_checked : rotationDot_22_9.ExtendedCheck nodes 3 := by decide
def rotationDot_22_10 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_22_10_checked : rotationDot_22_10.ExtendedCheck nodes 3 := by decide
def rotationDot_22_11 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2426,11,11][i]?.getD 0
  accumulator := fun i => #[11,2426,2426,2426][i]?.getD 0
theorem rotationDot_22_11_checked : rotationDot_22_11.ExtendedCheck nodes 3 := by decide
def rotationDot_22_12 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_12_checked : rotationDot_22_12.ExtendedCheck nodes 3 := by decide
def rotationDot_22_13 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2419,11,2390][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2517][i]?.getD 0
theorem rotationDot_22_13_checked : rotationDot_22_13.ExtendedCheck nodes 3 := by decide
def rotationDot_22_14 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_22_14_checked : rotationDot_22_14.ExtendedCheck nodes 3 := by decide
def rotationDot_22_15 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2397][i]?.getD 0
  accumulator := fun i => #[11,11,11,2397][i]?.getD 0
theorem rotationDot_22_15_checked : rotationDot_22_15.ExtendedCheck nodes 3 := by decide
def rotationDot_22_16 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_22_16_checked : rotationDot_22_16.ExtendedCheck nodes 3 := by decide
def rotationDot_22_17 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2433,11,11][i]?.getD 0
  accumulator := fun i => #[11,2433,2433,2433][i]?.getD 0
theorem rotationDot_22_17_checked : rotationDot_22_17.ExtendedCheck nodes 3 := by decide
def rotationDot_22_18 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_22_18_checked : rotationDot_22_18.ExtendedCheck nodes 3 := by decide
def rotationDot_22_19 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,2402][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2523][i]?.getD 0
theorem rotationDot_22_19_checked : rotationDot_22_19.ExtendedCheck nodes 3 := by decide
def rotationDot_22_20 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_22_20_checked : rotationDot_22_20.ExtendedCheck nodes 3 := by decide
def rotationDot_22_21 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_22_21_checked : rotationDot_22_21.ExtendedCheck nodes 3 := by decide
def rotationDot_22_22 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,710][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2526][i]?.getD 0
theorem rotationDot_22_22_checked : rotationDot_22_22.ExtendedCheck nodes 3 := by decide
def rotationDot_22_23 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_22_23_checked : rotationDot_22_23.ExtendedCheck nodes 3 := by decide
def rotationDot_22_24 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2409][i]?.getD 0
  accumulator := fun i => #[11,11,11,2409][i]?.getD 0
theorem rotationDot_22_24_checked : rotationDot_22_24.ExtendedCheck nodes 3 := by decide
def rotationDot_22_25 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,710][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2526][i]?.getD 0
theorem rotationDot_22_25_checked : rotationDot_22_25.ExtendedCheck nodes 3 := by decide
def rotationDot_22_26 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_22_26_checked : rotationDot_22_26.ExtendedCheck nodes 3 := by decide
def rotationDot_22_27 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2409][i]?.getD 0
  accumulator := fun i => #[11,11,11,2409][i]?.getD 0
theorem rotationDot_22_27_checked : rotationDot_22_27.ExtendedCheck nodes 3 := by decide
def rotationDot_22_28 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,2402][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2523][i]?.getD 0
theorem rotationDot_22_28_checked : rotationDot_22_28.ExtendedCheck nodes 3 := by decide
def rotationDot_22_29 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_22_29_checked : rotationDot_22_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow22 : Array DotRecipe := #[rotationDot_22_0,rotationDot_22_1,rotationDot_22_2,rotationDot_22_3,rotationDot_22_4,rotationDot_22_5,rotationDot_22_6,rotationDot_22_7,rotationDot_22_8,rotationDot_22_9,rotationDot_22_10,rotationDot_22_11,rotationDot_22_12,rotationDot_22_13,rotationDot_22_14,rotationDot_22_15,rotationDot_22_16,rotationDot_22_17,rotationDot_22_18,rotationDot_22_19,rotationDot_22_20,rotationDot_22_21,rotationDot_22_22,rotationDot_22_23,rotationDot_22_24,rotationDot_22_25,rotationDot_22_26,rotationDot_22_27,rotationDot_22_28,rotationDot_22_29]
theorem rotationDotsRow22_checked (j : Fin 30) :
    (rotationDotsRow22[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_22_0_checked
  · exact rotationDot_22_1_checked
  · exact rotationDot_22_2_checked
  · exact rotationDot_22_3_checked
  · exact rotationDot_22_4_checked
  · exact rotationDot_22_5_checked
  · exact rotationDot_22_6_checked
  · exact rotationDot_22_7_checked
  · exact rotationDot_22_8_checked
  · exact rotationDot_22_9_checked
  · exact rotationDot_22_10_checked
  · exact rotationDot_22_11_checked
  · exact rotationDot_22_12_checked
  · exact rotationDot_22_13_checked
  · exact rotationDot_22_14_checked
  · exact rotationDot_22_15_checked
  · exact rotationDot_22_16_checked
  · exact rotationDot_22_17_checked
  · exact rotationDot_22_18_checked
  · exact rotationDot_22_19_checked
  · exact rotationDot_22_20_checked
  · exact rotationDot_22_21_checked
  · exact rotationDot_22_22_checked
  · exact rotationDot_22_23_checked
  · exact rotationDot_22_24_checked
  · exact rotationDot_22_25_checked
  · exact rotationDot_22_26_checked
  · exact rotationDot_22_27_checked
  · exact rotationDot_22_28_checked
  · exact rotationDot_22_29_checked
def rotationDot_23_0 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,1461,11][i]?.getD 0
  accumulator := fun i => #[11,11,1461,1461][i]?.getD 0
theorem rotationDot_23_0_checked : rotationDot_23_0.ExtendedCheck nodes 3 := by decide
def rotationDot_23_1 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2455,11,11][i]?.getD 0
  accumulator := fun i => #[11,2455,2455,2455][i]?.getD 0
theorem rotationDot_23_1_checked : rotationDot_23_1.ExtendedCheck nodes 3 := by decide
def rotationDot_23_2 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_23_2_checked : rotationDot_23_2.ExtendedCheck nodes 3 := by decide
def rotationDot_23_3 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2537,11][i]?.getD 0
  accumulator := fun i => #[11,11,2537,2537][i]?.getD 0
theorem rotationDot_23_3_checked : rotationDot_23_3.ExtendedCheck nodes 3 := by decide
def rotationDot_23_4 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[10,11,11][i]?.getD 0
  accumulator := fun i => #[11,10,10,10][i]?.getD 0
theorem rotationDot_23_4_checked : rotationDot_23_4.ExtendedCheck nodes 3 := by decide
def rotationDot_23_5 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_23_5_checked : rotationDot_23_5.ExtendedCheck nodes 3 := by decide
def rotationDot_23_6 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_23_6_checked : rotationDot_23_6.ExtendedCheck nodes 3 := by decide
def rotationDot_23_7 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_23_7_checked : rotationDot_23_7.ExtendedCheck nodes 3 := by decide
def rotationDot_23_8 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2543,11][i]?.getD 0
  accumulator := fun i => #[11,11,2543,2543][i]?.getD 0
theorem rotationDot_23_8_checked : rotationDot_23_8.ExtendedCheck nodes 3 := by decide
def rotationDot_23_9 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_23_9_checked : rotationDot_23_9.ExtendedCheck nodes 3 := by decide
def rotationDot_23_10 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_23_10_checked : rotationDot_23_10.ExtendedCheck nodes 3 := by decide
def rotationDot_23_11 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2420,11,11][i]?.getD 0
  accumulator := fun i => #[11,2420,2420,2420][i]?.getD 0
theorem rotationDot_23_11_checked : rotationDot_23_11.ExtendedCheck nodes 3 := by decide
def rotationDot_23_12 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_23_12_checked : rotationDot_23_12.ExtendedCheck nodes 3 := by decide
def rotationDot_23_13 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_23_13_checked : rotationDot_23_13.ExtendedCheck nodes 3 := by decide
def rotationDot_23_14 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2550,11][i]?.getD 0
  accumulator := fun i => #[11,11,2550,2550][i]?.getD 0
theorem rotationDot_23_14_checked : rotationDot_23_14.ExtendedCheck nodes 3 := by decide
def rotationDot_23_15 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_23_15_checked : rotationDot_23_15.ExtendedCheck nodes 3 := by decide
def rotationDot_23_16 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2462,11,11][i]?.getD 0
  accumulator := fun i => #[11,2462,2462,2462][i]?.getD 0
theorem rotationDot_23_16_checked : rotationDot_23_16.ExtendedCheck nodes 3 := by decide
def rotationDot_23_17 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2423,11,11][i]?.getD 0
  accumulator := fun i => #[11,2423,2423,2423][i]?.getD 0
theorem rotationDot_23_17_checked : rotationDot_23_17.ExtendedCheck nodes 3 := by decide
def rotationDot_23_18 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_23_18_checked : rotationDot_23_18.ExtendedCheck nodes 3 := by decide
def rotationDot_23_19 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_23_19_checked : rotationDot_23_19.ExtendedCheck nodes 3 := by decide
def rotationDot_23_20 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[403,2557,11][i]?.getD 0
  accumulator := fun i => #[11,403,2558,2558][i]?.getD 0
theorem rotationDot_23_20_checked : rotationDot_23_20.ExtendedCheck nodes 3 := by decide
def rotationDot_23_21 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_23_21_checked : rotationDot_23_21.ExtendedCheck nodes 3 := by decide
def rotationDot_23_22 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_23_22_checked : rotationDot_23_22.ExtendedCheck nodes 3 := by decide
def rotationDot_23_23 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[403,2562,11][i]?.getD 0
  accumulator := fun i => #[11,403,2563,2563][i]?.getD 0
theorem rotationDot_23_23_checked : rotationDot_23_23.ExtendedCheck nodes 3 := by decide
def rotationDot_23_24 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_23_24_checked : rotationDot_23_24.ExtendedCheck nodes 3 := by decide
def rotationDot_23_25 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_23_25_checked : rotationDot_23_25.ExtendedCheck nodes 3 := by decide
def rotationDot_23_26 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2435,2562,11][i]?.getD 0
  accumulator := fun i => #[11,2435,2567,2567][i]?.getD 0
theorem rotationDot_23_26_checked : rotationDot_23_26.ExtendedCheck nodes 3 := by decide
def rotationDot_23_27 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_23_27_checked : rotationDot_23_27.ExtendedCheck nodes 3 := by decide
def rotationDot_23_28 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2476,11,11][i]?.getD 0
  accumulator := fun i => #[11,2476,2476,2476][i]?.getD 0
theorem rotationDot_23_28_checked : rotationDot_23_28.ExtendedCheck nodes 3 := by decide
def rotationDot_23_29 : DotRecipe where
  left := fun i => #[10,1461,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2435,2557,11][i]?.getD 0
  accumulator := fun i => #[11,2435,2571,2571][i]?.getD 0
theorem rotationDot_23_29_checked : rotationDot_23_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow23 : Array DotRecipe := #[rotationDot_23_0,rotationDot_23_1,rotationDot_23_2,rotationDot_23_3,rotationDot_23_4,rotationDot_23_5,rotationDot_23_6,rotationDot_23_7,rotationDot_23_8,rotationDot_23_9,rotationDot_23_10,rotationDot_23_11,rotationDot_23_12,rotationDot_23_13,rotationDot_23_14,rotationDot_23_15,rotationDot_23_16,rotationDot_23_17,rotationDot_23_18,rotationDot_23_19,rotationDot_23_20,rotationDot_23_21,rotationDot_23_22,rotationDot_23_23,rotationDot_23_24,rotationDot_23_25,rotationDot_23_26,rotationDot_23_27,rotationDot_23_28,rotationDot_23_29]
theorem rotationDotsRow23_checked (j : Fin 30) :
    (rotationDotsRow23[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_23_0_checked
  · exact rotationDot_23_1_checked
  · exact rotationDot_23_2_checked
  · exact rotationDot_23_3_checked
  · exact rotationDot_23_4_checked
  · exact rotationDot_23_5_checked
  · exact rotationDot_23_6_checked
  · exact rotationDot_23_7_checked
  · exact rotationDot_23_8_checked
  · exact rotationDot_23_9_checked
  · exact rotationDot_23_10_checked
  · exact rotationDot_23_11_checked
  · exact rotationDot_23_12_checked
  · exact rotationDot_23_13_checked
  · exact rotationDot_23_14_checked
  · exact rotationDot_23_15_checked
  · exact rotationDot_23_16_checked
  · exact rotationDot_23_17_checked
  · exact rotationDot_23_18_checked
  · exact rotationDot_23_19_checked
  · exact rotationDot_23_20_checked
  · exact rotationDot_23_21_checked
  · exact rotationDot_23_22_checked
  · exact rotationDot_23_23_checked
  · exact rotationDot_23_24_checked
  · exact rotationDot_23_25_checked
  · exact rotationDot_23_26_checked
  · exact rotationDot_23_27_checked
  · exact rotationDot_23_28_checked
  · exact rotationDot_23_29_checked
def rotationDot_24_0 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_24_0_checked : rotationDot_24_0.ExtendedCheck nodes 3 := by decide
def rotationDot_24_1 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_1_checked : rotationDot_24_1.ExtendedCheck nodes 3 := by decide
def rotationDot_24_2 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_2_checked : rotationDot_24_2.ExtendedCheck nodes 3 := by decide
def rotationDot_24_3 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2156,11][i]?.getD 0
  accumulator := fun i => #[11,11,2156,2156][i]?.getD 0
theorem rotationDot_24_3_checked : rotationDot_24_3.ExtendedCheck nodes 3 := by decide
def rotationDot_24_4 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_4_checked : rotationDot_24_4.ExtendedCheck nodes 3 := by decide
def rotationDot_24_5 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_5_checked : rotationDot_24_5.ExtendedCheck nodes 3 := by decide
def rotationDot_24_6 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_24_6_checked : rotationDot_24_6.ExtendedCheck nodes 3 := by decide
def rotationDot_24_7 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2575][i]?.getD 0
  accumulator := fun i => #[11,11,11,2575][i]?.getD 0
theorem rotationDot_24_7_checked : rotationDot_24_7.ExtendedCheck nodes 3 := by decide
def rotationDot_24_8 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2171,11][i]?.getD 0
  accumulator := fun i => #[11,11,2171,2171][i]?.getD 0
theorem rotationDot_24_8_checked : rotationDot_24_8.ExtendedCheck nodes 3 := by decide
def rotationDot_24_9 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2385,2543][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2578][i]?.getD 0
theorem rotationDot_24_9_checked : rotationDot_24_9.ExtendedCheck nodes 3 := by decide
def rotationDot_24_10 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_10_checked : rotationDot_24_10.ExtendedCheck nodes 3 := by decide
def rotationDot_24_11 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_11_checked : rotationDot_24_11.ExtendedCheck nodes 3 := by decide
def rotationDot_24_12 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_24_12_checked : rotationDot_24_12.ExtendedCheck nodes 3 := by decide
def rotationDot_24_13 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,2543][i]?.getD 0
  accumulator := fun i => #[11,11,11,2543][i]?.getD 0
theorem rotationDot_24_13_checked : rotationDot_24_13.ExtendedCheck nodes 3 := by decide
def rotationDot_24_14 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2395,11][i]?.getD 0
  accumulator := fun i => #[11,11,2395,2395][i]?.getD 0
theorem rotationDot_24_14_checked : rotationDot_24_14.ExtendedCheck nodes 3 := by decide
def rotationDot_24_15 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2385,2550][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2583][i]?.getD 0
theorem rotationDot_24_15_checked : rotationDot_24_15.ExtendedCheck nodes 3 := by decide
def rotationDot_24_16 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_16_checked : rotationDot_24_16.ExtendedCheck nodes 3 := by decide
def rotationDot_24_17 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_24_17_checked : rotationDot_24_17.ExtendedCheck nodes 3 := by decide
def rotationDot_24_18 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,2557][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2585][i]?.getD 0
theorem rotationDot_24_18_checked : rotationDot_24_18.ExtendedCheck nodes 3 := by decide
def rotationDot_24_19 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2587][i]?.getD 0
  accumulator := fun i => #[11,11,11,2587][i]?.getD 0
theorem rotationDot_24_19_checked : rotationDot_24_19.ExtendedCheck nodes 3 := by decide
def rotationDot_24_20 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_24_20_checked : rotationDot_24_20.ExtendedCheck nodes 3 := by decide
def rotationDot_24_21 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,2557][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2585][i]?.getD 0
theorem rotationDot_24_21_checked : rotationDot_24_21.ExtendedCheck nodes 3 := by decide
def rotationDot_24_22 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2557][i]?.getD 0
  accumulator := fun i => #[11,11,11,2557][i]?.getD 0
theorem rotationDot_24_22_checked : rotationDot_24_22.ExtendedCheck nodes 3 := by decide
def rotationDot_24_23 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_24_23_checked : rotationDot_24_23.ExtendedCheck nodes 3 := by decide
def rotationDot_24_24 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2562][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2592][i]?.getD 0
theorem rotationDot_24_24_checked : rotationDot_24_24.ExtendedCheck nodes 3 := by decide
def rotationDot_24_25 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2557][i]?.getD 0
  accumulator := fun i => #[11,11,11,2557][i]?.getD 0
theorem rotationDot_24_25_checked : rotationDot_24_25.ExtendedCheck nodes 3 := by decide
def rotationDot_24_26 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_24_26_checked : rotationDot_24_26.ExtendedCheck nodes 3 := by decide
def rotationDot_24_27 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2562][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2592][i]?.getD 0
theorem rotationDot_24_27_checked : rotationDot_24_27.ExtendedCheck nodes 3 := by decide
def rotationDot_24_28 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2587][i]?.getD 0
  accumulator := fun i => #[11,11,11,2587][i]?.getD 0
theorem rotationDot_24_28_checked : rotationDot_24_28.ExtendedCheck nodes 3 := by decide
def rotationDot_24_29 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_24_29_checked : rotationDot_24_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow24 : Array DotRecipe := #[rotationDot_24_0,rotationDot_24_1,rotationDot_24_2,rotationDot_24_3,rotationDot_24_4,rotationDot_24_5,rotationDot_24_6,rotationDot_24_7,rotationDot_24_8,rotationDot_24_9,rotationDot_24_10,rotationDot_24_11,rotationDot_24_12,rotationDot_24_13,rotationDot_24_14,rotationDot_24_15,rotationDot_24_16,rotationDot_24_17,rotationDot_24_18,rotationDot_24_19,rotationDot_24_20,rotationDot_24_21,rotationDot_24_22,rotationDot_24_23,rotationDot_24_24,rotationDot_24_25,rotationDot_24_26,rotationDot_24_27,rotationDot_24_28,rotationDot_24_29]
theorem rotationDotsRow24_checked (j : Fin 30) :
    (rotationDotsRow24[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_24_0_checked
  · exact rotationDot_24_1_checked
  · exact rotationDot_24_2_checked
  · exact rotationDot_24_3_checked
  · exact rotationDot_24_4_checked
  · exact rotationDot_24_5_checked
  · exact rotationDot_24_6_checked
  · exact rotationDot_24_7_checked
  · exact rotationDot_24_8_checked
  · exact rotationDot_24_9_checked
  · exact rotationDot_24_10_checked
  · exact rotationDot_24_11_checked
  · exact rotationDot_24_12_checked
  · exact rotationDot_24_13_checked
  · exact rotationDot_24_14_checked
  · exact rotationDot_24_15_checked
  · exact rotationDot_24_16_checked
  · exact rotationDot_24_17_checked
  · exact rotationDot_24_18_checked
  · exact rotationDot_24_19_checked
  · exact rotationDot_24_20_checked
  · exact rotationDot_24_21_checked
  · exact rotationDot_24_22_checked
  · exact rotationDot_24_23_checked
  · exact rotationDot_24_24_checked
  · exact rotationDot_24_25_checked
  · exact rotationDot_24_26_checked
  · exact rotationDot_24_27_checked
  · exact rotationDot_24_28_checked
  · exact rotationDot_24_29_checked
def rotationDot_25_0 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_0_checked : rotationDot_25_0.ExtendedCheck nodes 3 := by decide
def rotationDot_25_1 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2417,11,11][i]?.getD 0
  accumulator := fun i => #[11,2417,2417,2417][i]?.getD 0
theorem rotationDot_25_1_checked : rotationDot_25_1.ExtendedCheck nodes 3 := by decide
def rotationDot_25_2 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_2_checked : rotationDot_25_2.ExtendedCheck nodes 3 := by decide
def rotationDot_25_3 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_3_checked : rotationDot_25_3.ExtendedCheck nodes 3 := by decide
def rotationDot_25_4 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_25_4_checked : rotationDot_25_4.ExtendedCheck nodes 3 := by decide
def rotationDot_25_5 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_5_checked : rotationDot_25_5.ExtendedCheck nodes 3 := by decide
def rotationDot_25_6 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_6_checked : rotationDot_25_6.ExtendedCheck nodes 3 := by decide
def rotationDot_25_7 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2419,11,2387][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2512][i]?.getD 0
theorem rotationDot_25_7_checked : rotationDot_25_7.ExtendedCheck nodes 3 := by decide
def rotationDot_25_8 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_8_checked : rotationDot_25_8.ExtendedCheck nodes 3 := by decide
def rotationDot_25_9 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,2390][i]?.getD 0
  accumulator := fun i => #[11,11,11,2390][i]?.getD 0
theorem rotationDot_25_9_checked : rotationDot_25_9.ExtendedCheck nodes 3 := by decide
def rotationDot_25_10 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_25_10_checked : rotationDot_25_10.ExtendedCheck nodes 3 := by decide
def rotationDot_25_11 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2426,11,11][i]?.getD 0
  accumulator := fun i => #[11,2426,2426,2426][i]?.getD 0
theorem rotationDot_25_11_checked : rotationDot_25_11.ExtendedCheck nodes 3 := by decide
def rotationDot_25_12 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_12_checked : rotationDot_25_12.ExtendedCheck nodes 3 := by decide
def rotationDot_25_13 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2419,11,2390][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2517][i]?.getD 0
theorem rotationDot_25_13_checked : rotationDot_25_13.ExtendedCheck nodes 3 := by decide
def rotationDot_25_14 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_25_14_checked : rotationDot_25_14.ExtendedCheck nodes 3 := by decide
def rotationDot_25_15 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2397][i]?.getD 0
  accumulator := fun i => #[11,11,11,2397][i]?.getD 0
theorem rotationDot_25_15_checked : rotationDot_25_15.ExtendedCheck nodes 3 := by decide
def rotationDot_25_16 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_25_16_checked : rotationDot_25_16.ExtendedCheck nodes 3 := by decide
def rotationDot_25_17 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2433,11,11][i]?.getD 0
  accumulator := fun i => #[11,2433,2433,2433][i]?.getD 0
theorem rotationDot_25_17_checked : rotationDot_25_17.ExtendedCheck nodes 3 := by decide
def rotationDot_25_18 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_25_18_checked : rotationDot_25_18.ExtendedCheck nodes 3 := by decide
def rotationDot_25_19 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,2402][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2523][i]?.getD 0
theorem rotationDot_25_19_checked : rotationDot_25_19.ExtendedCheck nodes 3 := by decide
def rotationDot_25_20 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_25_20_checked : rotationDot_25_20.ExtendedCheck nodes 3 := by decide
def rotationDot_25_21 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,710][i]?.getD 0
  accumulator := fun i => #[11,11,11,710][i]?.getD 0
theorem rotationDot_25_21_checked : rotationDot_25_21.ExtendedCheck nodes 3 := by decide
def rotationDot_25_22 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,710][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2526][i]?.getD 0
theorem rotationDot_25_22_checked : rotationDot_25_22.ExtendedCheck nodes 3 := by decide
def rotationDot_25_23 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_25_23_checked : rotationDot_25_23.ExtendedCheck nodes 3 := by decide
def rotationDot_25_24 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2409][i]?.getD 0
  accumulator := fun i => #[11,11,11,2409][i]?.getD 0
theorem rotationDot_25_24_checked : rotationDot_25_24.ExtendedCheck nodes 3 := by decide
def rotationDot_25_25 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,710][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2526][i]?.getD 0
theorem rotationDot_25_25_checked : rotationDot_25_25.ExtendedCheck nodes 3 := by decide
def rotationDot_25_26 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_25_26_checked : rotationDot_25_26.ExtendedCheck nodes 3 := by decide
def rotationDot_25_27 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2409][i]?.getD 0
  accumulator := fun i => #[11,11,11,2409][i]?.getD 0
theorem rotationDot_25_27_checked : rotationDot_25_27.ExtendedCheck nodes 3 := by decide
def rotationDot_25_28 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,2402][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2523][i]?.getD 0
theorem rotationDot_25_28_checked : rotationDot_25_28.ExtendedCheck nodes 3 := by decide
def rotationDot_25_29 : DotRecipe where
  left := fun i => #[1048,11,14][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_25_29_checked : rotationDot_25_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow25 : Array DotRecipe := #[rotationDot_25_0,rotationDot_25_1,rotationDot_25_2,rotationDot_25_3,rotationDot_25_4,rotationDot_25_5,rotationDot_25_6,rotationDot_25_7,rotationDot_25_8,rotationDot_25_9,rotationDot_25_10,rotationDot_25_11,rotationDot_25_12,rotationDot_25_13,rotationDot_25_14,rotationDot_25_15,rotationDot_25_16,rotationDot_25_17,rotationDot_25_18,rotationDot_25_19,rotationDot_25_20,rotationDot_25_21,rotationDot_25_22,rotationDot_25_23,rotationDot_25_24,rotationDot_25_25,rotationDot_25_26,rotationDot_25_27,rotationDot_25_28,rotationDot_25_29]
theorem rotationDotsRow25_checked (j : Fin 30) :
    (rotationDotsRow25[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_25_0_checked
  · exact rotationDot_25_1_checked
  · exact rotationDot_25_2_checked
  · exact rotationDot_25_3_checked
  · exact rotationDot_25_4_checked
  · exact rotationDot_25_5_checked
  · exact rotationDot_25_6_checked
  · exact rotationDot_25_7_checked
  · exact rotationDot_25_8_checked
  · exact rotationDot_25_9_checked
  · exact rotationDot_25_10_checked
  · exact rotationDot_25_11_checked
  · exact rotationDot_25_12_checked
  · exact rotationDot_25_13_checked
  · exact rotationDot_25_14_checked
  · exact rotationDot_25_15_checked
  · exact rotationDot_25_16_checked
  · exact rotationDot_25_17_checked
  · exact rotationDot_25_18_checked
  · exact rotationDot_25_19_checked
  · exact rotationDot_25_20_checked
  · exact rotationDot_25_21_checked
  · exact rotationDot_25_22_checked
  · exact rotationDot_25_23_checked
  · exact rotationDot_25_24_checked
  · exact rotationDot_25_25_checked
  · exact rotationDot_25_26_checked
  · exact rotationDot_25_27_checked
  · exact rotationDot_25_28_checked
  · exact rotationDot_25_29_checked
def rotationDot_26_0 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,1461,11][i]?.getD 0
  accumulator := fun i => #[11,11,1461,1461][i]?.getD 0
theorem rotationDot_26_0_checked : rotationDot_26_0.ExtendedCheck nodes 3 := by decide
def rotationDot_26_1 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2457,11,11][i]?.getD 0
  accumulator := fun i => #[11,2457,2457,2457][i]?.getD 0
theorem rotationDot_26_1_checked : rotationDot_26_1.ExtendedCheck nodes 3 := by decide
def rotationDot_26_2 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_26_2_checked : rotationDot_26_2.ExtendedCheck nodes 3 := by decide
def rotationDot_26_3 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2537,11][i]?.getD 0
  accumulator := fun i => #[11,11,2537,2537][i]?.getD 0
theorem rotationDot_26_3_checked : rotationDot_26_3.ExtendedCheck nodes 3 := by decide
def rotationDot_26_4 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[14,11,11][i]?.getD 0
  accumulator := fun i => #[11,14,14,14][i]?.getD 0
theorem rotationDot_26_4_checked : rotationDot_26_4.ExtendedCheck nodes 3 := by decide
def rotationDot_26_5 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_26_5_checked : rotationDot_26_5.ExtendedCheck nodes 3 := by decide
def rotationDot_26_6 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_26_6_checked : rotationDot_26_6.ExtendedCheck nodes 3 := by decide
def rotationDot_26_7 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_26_7_checked : rotationDot_26_7.ExtendedCheck nodes 3 := by decide
def rotationDot_26_8 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2543,11][i]?.getD 0
  accumulator := fun i => #[11,11,2543,2543][i]?.getD 0
theorem rotationDot_26_8_checked : rotationDot_26_8.ExtendedCheck nodes 3 := by decide
def rotationDot_26_9 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_26_9_checked : rotationDot_26_9.ExtendedCheck nodes 3 := by decide
def rotationDot_26_10 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_26_10_checked : rotationDot_26_10.ExtendedCheck nodes 3 := by decide
def rotationDot_26_11 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2387,11,11][i]?.getD 0
  accumulator := fun i => #[11,2387,2387,2387][i]?.getD 0
theorem rotationDot_26_11_checked : rotationDot_26_11.ExtendedCheck nodes 3 := by decide
def rotationDot_26_12 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_26_12_checked : rotationDot_26_12.ExtendedCheck nodes 3 := by decide
def rotationDot_26_13 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_26_13_checked : rotationDot_26_13.ExtendedCheck nodes 3 := by decide
def rotationDot_26_14 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2550,11][i]?.getD 0
  accumulator := fun i => #[11,11,2550,2550][i]?.getD 0
theorem rotationDot_26_14_checked : rotationDot_26_14.ExtendedCheck nodes 3 := by decide
def rotationDot_26_15 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2540,11][i]?.getD 0
  accumulator := fun i => #[11,11,2540,2540][i]?.getD 0
theorem rotationDot_26_15_checked : rotationDot_26_15.ExtendedCheck nodes 3 := by decide
def rotationDot_26_16 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_26_16_checked : rotationDot_26_16.ExtendedCheck nodes 3 := by decide
def rotationDot_26_17 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2390,11,11][i]?.getD 0
  accumulator := fun i => #[11,2390,2390,2390][i]?.getD 0
theorem rotationDot_26_17_checked : rotationDot_26_17.ExtendedCheck nodes 3 := by decide
def rotationDot_26_18 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_26_18_checked : rotationDot_26_18.ExtendedCheck nodes 3 := by decide
def rotationDot_26_19 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_26_19_checked : rotationDot_26_19.ExtendedCheck nodes 3 := by decide
def rotationDot_26_20 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2402,2557,11][i]?.getD 0
  accumulator := fun i => #[11,2402,2637,2637][i]?.getD 0
theorem rotationDot_26_20_checked : rotationDot_26_20.ExtendedCheck nodes 3 := by decide
def rotationDot_26_21 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_26_21_checked : rotationDot_26_21.ExtendedCheck nodes 3 := by decide
def rotationDot_26_22 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_26_22_checked : rotationDot_26_22.ExtendedCheck nodes 3 := by decide
def rotationDot_26_23 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2402,2562,11][i]?.getD 0
  accumulator := fun i => #[11,2402,2640,2640][i]?.getD 0
theorem rotationDot_26_23_checked : rotationDot_26_23.ExtendedCheck nodes 3 := by decide
def rotationDot_26_24 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_26_24_checked : rotationDot_26_24.ExtendedCheck nodes 3 := by decide
def rotationDot_26_25 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_26_25_checked : rotationDot_26_25.ExtendedCheck nodes 3 := by decide
def rotationDot_26_26 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[710,2562,11][i]?.getD 0
  accumulator := fun i => #[11,710,2644,2644][i]?.getD 0
theorem rotationDot_26_26_checked : rotationDot_26_26.ExtendedCheck nodes 3 := by decide
def rotationDot_26_27 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2555,11][i]?.getD 0
  accumulator := fun i => #[11,11,2555,2555][i]?.getD 0
theorem rotationDot_26_27_checked : rotationDot_26_27.ExtendedCheck nodes 3 := by decide
def rotationDot_26_28 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_26_28_checked : rotationDot_26_28.ExtendedCheck nodes 3 := by decide
def rotationDot_26_29 : DotRecipe where
  left := fun i => #[14,1461,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[710,2557,11][i]?.getD 0
  accumulator := fun i => #[11,710,2648,2648][i]?.getD 0
theorem rotationDot_26_29_checked : rotationDot_26_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow26 : Array DotRecipe := #[rotationDot_26_0,rotationDot_26_1,rotationDot_26_2,rotationDot_26_3,rotationDot_26_4,rotationDot_26_5,rotationDot_26_6,rotationDot_26_7,rotationDot_26_8,rotationDot_26_9,rotationDot_26_10,rotationDot_26_11,rotationDot_26_12,rotationDot_26_13,rotationDot_26_14,rotationDot_26_15,rotationDot_26_16,rotationDot_26_17,rotationDot_26_18,rotationDot_26_19,rotationDot_26_20,rotationDot_26_21,rotationDot_26_22,rotationDot_26_23,rotationDot_26_24,rotationDot_26_25,rotationDot_26_26,rotationDot_26_27,rotationDot_26_28,rotationDot_26_29]
theorem rotationDotsRow26_checked (j : Fin 30) :
    (rotationDotsRow26[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_26_0_checked
  · exact rotationDot_26_1_checked
  · exact rotationDot_26_2_checked
  · exact rotationDot_26_3_checked
  · exact rotationDot_26_4_checked
  · exact rotationDot_26_5_checked
  · exact rotationDot_26_6_checked
  · exact rotationDot_26_7_checked
  · exact rotationDot_26_8_checked
  · exact rotationDot_26_9_checked
  · exact rotationDot_26_10_checked
  · exact rotationDot_26_11_checked
  · exact rotationDot_26_12_checked
  · exact rotationDot_26_13_checked
  · exact rotationDot_26_14_checked
  · exact rotationDot_26_15_checked
  · exact rotationDot_26_16_checked
  · exact rotationDot_26_17_checked
  · exact rotationDot_26_18_checked
  · exact rotationDot_26_19_checked
  · exact rotationDot_26_20_checked
  · exact rotationDot_26_21_checked
  · exact rotationDot_26_22_checked
  · exact rotationDot_26_23_checked
  · exact rotationDot_26_24_checked
  · exact rotationDot_26_25_checked
  · exact rotationDot_26_26_checked
  · exact rotationDot_26_27_checked
  · exact rotationDot_26_28_checked
  · exact rotationDot_26_29_checked
def rotationDot_27_0 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,12,11][i]?.getD 0
  accumulator := fun i => #[11,11,12,12][i]?.getD 0
theorem rotationDot_27_0_checked : rotationDot_27_0.ExtendedCheck nodes 3 := by decide
def rotationDot_27_1 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_1_checked : rotationDot_27_1.ExtendedCheck nodes 3 := by decide
def rotationDot_27_2 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_2_checked : rotationDot_27_2.ExtendedCheck nodes 3 := by decide
def rotationDot_27_3 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2156,11][i]?.getD 0
  accumulator := fun i => #[11,11,2156,2156][i]?.getD 0
theorem rotationDot_27_3_checked : rotationDot_27_3.ExtendedCheck nodes 3 := by decide
def rotationDot_27_4 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_4_checked : rotationDot_27_4.ExtendedCheck nodes 3 := by decide
def rotationDot_27_5 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_5_checked : rotationDot_27_5.ExtendedCheck nodes 3 := by decide
def rotationDot_27_6 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_27_6_checked : rotationDot_27_6.ExtendedCheck nodes 3 := by decide
def rotationDot_27_7 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[11,11,2575][i]?.getD 0
  accumulator := fun i => #[11,11,11,2575][i]?.getD 0
theorem rotationDot_27_7_checked : rotationDot_27_7.ExtendedCheck nodes 3 := by decide
def rotationDot_27_8 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2171,11][i]?.getD 0
  accumulator := fun i => #[11,11,2171,2171][i]?.getD 0
theorem rotationDot_27_8_checked : rotationDot_27_8.ExtendedCheck nodes 3 := by decide
def rotationDot_27_9 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2385,2543][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2578][i]?.getD 0
theorem rotationDot_27_9_checked : rotationDot_27_9.ExtendedCheck nodes 3 := by decide
def rotationDot_27_10 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_10_checked : rotationDot_27_10.ExtendedCheck nodes 3 := by decide
def rotationDot_27_11 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_11_checked : rotationDot_27_11.ExtendedCheck nodes 3 := by decide
def rotationDot_27_12 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2385,11][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2385][i]?.getD 0
theorem rotationDot_27_12_checked : rotationDot_27_12.ExtendedCheck nodes 3 := by decide
def rotationDot_27_13 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[11,11,2543][i]?.getD 0
  accumulator := fun i => #[11,11,11,2543][i]?.getD 0
theorem rotationDot_27_13_checked : rotationDot_27_13.ExtendedCheck nodes 3 := by decide
def rotationDot_27_14 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2395,11][i]?.getD 0
  accumulator := fun i => #[11,11,2395,2395][i]?.getD 0
theorem rotationDot_27_14_checked : rotationDot_27_14.ExtendedCheck nodes 3 := by decide
def rotationDot_27_15 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2385,2550][i]?.getD 0
  accumulator := fun i => #[11,11,2385,2583][i]?.getD 0
theorem rotationDot_27_15_checked : rotationDot_27_15.ExtendedCheck nodes 3 := by decide
def rotationDot_27_16 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_16_checked : rotationDot_27_16.ExtendedCheck nodes 3 := by decide
def rotationDot_27_17 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_27_17_checked : rotationDot_27_17.ExtendedCheck nodes 3 := by decide
def rotationDot_27_18 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,2557][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2585][i]?.getD 0
theorem rotationDot_27_18_checked : rotationDot_27_18.ExtendedCheck nodes 3 := by decide
def rotationDot_27_19 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2587][i]?.getD 0
  accumulator := fun i => #[11,11,11,2587][i]?.getD 0
theorem rotationDot_27_19_checked : rotationDot_27_19.ExtendedCheck nodes 3 := by decide
def rotationDot_27_20 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_27_20_checked : rotationDot_27_20.ExtendedCheck nodes 3 := by decide
def rotationDot_27_21 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2158,2557][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2585][i]?.getD 0
theorem rotationDot_27_21_checked : rotationDot_27_21.ExtendedCheck nodes 3 := by decide
def rotationDot_27_22 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2557][i]?.getD 0
  accumulator := fun i => #[11,11,11,2557][i]?.getD 0
theorem rotationDot_27_22_checked : rotationDot_27_22.ExtendedCheck nodes 3 := by decide
def rotationDot_27_23 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_27_23_checked : rotationDot_27_23.ExtendedCheck nodes 3 := by decide
def rotationDot_27_24 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2562][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2592][i]?.getD 0
theorem rotationDot_27_24_checked : rotationDot_27_24.ExtendedCheck nodes 3 := by decide
def rotationDot_27_25 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[11,11,2557][i]?.getD 0
  accumulator := fun i => #[11,11,11,2557][i]?.getD 0
theorem rotationDot_27_25_checked : rotationDot_27_25.ExtendedCheck nodes 3 := by decide
def rotationDot_27_26 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[11,2407,11][i]?.getD 0
  accumulator := fun i => #[11,11,2407,2407][i]?.getD 0
theorem rotationDot_27_26_checked : rotationDot_27_26.ExtendedCheck nodes 3 := by decide
def rotationDot_27_27 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2158,2562][i]?.getD 0
  accumulator := fun i => #[11,11,2158,2592][i]?.getD 0
theorem rotationDot_27_27_checked : rotationDot_27_27.ExtendedCheck nodes 3 := by decide
def rotationDot_27_28 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[11,11,2587][i]?.getD 0
  accumulator := fun i => #[11,11,11,2587][i]?.getD 0
theorem rotationDot_27_28_checked : rotationDot_27_28.ExtendedCheck nodes 3 := by decide
def rotationDot_27_29 : DotRecipe where
  left := fun i => #[11,12,1461][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[11,2188,11][i]?.getD 0
  accumulator := fun i => #[11,11,2188,2188][i]?.getD 0
theorem rotationDot_27_29_checked : rotationDot_27_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow27 : Array DotRecipe := #[rotationDot_27_0,rotationDot_27_1,rotationDot_27_2,rotationDot_27_3,rotationDot_27_4,rotationDot_27_5,rotationDot_27_6,rotationDot_27_7,rotationDot_27_8,rotationDot_27_9,rotationDot_27_10,rotationDot_27_11,rotationDot_27_12,rotationDot_27_13,rotationDot_27_14,rotationDot_27_15,rotationDot_27_16,rotationDot_27_17,rotationDot_27_18,rotationDot_27_19,rotationDot_27_20,rotationDot_27_21,rotationDot_27_22,rotationDot_27_23,rotationDot_27_24,rotationDot_27_25,rotationDot_27_26,rotationDot_27_27,rotationDot_27_28,rotationDot_27_29]
theorem rotationDotsRow27_checked (j : Fin 30) :
    (rotationDotsRow27[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_27_0_checked
  · exact rotationDot_27_1_checked
  · exact rotationDot_27_2_checked
  · exact rotationDot_27_3_checked
  · exact rotationDot_27_4_checked
  · exact rotationDot_27_5_checked
  · exact rotationDot_27_6_checked
  · exact rotationDot_27_7_checked
  · exact rotationDot_27_8_checked
  · exact rotationDot_27_9_checked
  · exact rotationDot_27_10_checked
  · exact rotationDot_27_11_checked
  · exact rotationDot_27_12_checked
  · exact rotationDot_27_13_checked
  · exact rotationDot_27_14_checked
  · exact rotationDot_27_15_checked
  · exact rotationDot_27_16_checked
  · exact rotationDot_27_17_checked
  · exact rotationDot_27_18_checked
  · exact rotationDot_27_19_checked
  · exact rotationDot_27_20_checked
  · exact rotationDot_27_21_checked
  · exact rotationDot_27_22_checked
  · exact rotationDot_27_23_checked
  · exact rotationDot_27_24_checked
  · exact rotationDot_27_25_checked
  · exact rotationDot_27_26_checked
  · exact rotationDot_27_27_checked
  · exact rotationDot_27_28_checked
  · exact rotationDot_27_29_checked
def rotationDot_28_0 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_0_checked : rotationDot_28_0.ExtendedCheck nodes 3 := by decide
def rotationDot_28_1 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2417,11,11][i]?.getD 0
  accumulator := fun i => #[11,2417,2417,2417][i]?.getD 0
theorem rotationDot_28_1_checked : rotationDot_28_1.ExtendedCheck nodes 3 := by decide
def rotationDot_28_2 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_2_checked : rotationDot_28_2.ExtendedCheck nodes 3 := by decide
def rotationDot_28_3 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_3_checked : rotationDot_28_3.ExtendedCheck nodes 3 := by decide
def rotationDot_28_4 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[1048,11,11][i]?.getD 0
  accumulator := fun i => #[11,1048,1048,1048][i]?.getD 0
theorem rotationDot_28_4_checked : rotationDot_28_4.ExtendedCheck nodes 3 := by decide
def rotationDot_28_5 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_5_checked : rotationDot_28_5.ExtendedCheck nodes 3 := by decide
def rotationDot_28_6 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_6_checked : rotationDot_28_6.ExtendedCheck nodes 3 := by decide
def rotationDot_28_7 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2419,11,2420][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2421][i]?.getD 0
theorem rotationDot_28_7_checked : rotationDot_28_7.ExtendedCheck nodes 3 := by decide
def rotationDot_28_8 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_8_checked : rotationDot_28_8.ExtendedCheck nodes 3 := by decide
def rotationDot_28_9 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,11,2423][i]?.getD 0
  accumulator := fun i => #[11,11,11,2423][i]?.getD 0
theorem rotationDot_28_9_checked : rotationDot_28_9.ExtendedCheck nodes 3 := by decide
def rotationDot_28_10 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_28_10_checked : rotationDot_28_10.ExtendedCheck nodes 3 := by decide
def rotationDot_28_11 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2426,11,11][i]?.getD 0
  accumulator := fun i => #[11,2426,2426,2426][i]?.getD 0
theorem rotationDot_28_11_checked : rotationDot_28_11.ExtendedCheck nodes 3 := by decide
def rotationDot_28_12 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_12_checked : rotationDot_28_12.ExtendedCheck nodes 3 := by decide
def rotationDot_28_13 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2419,11,2423][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2428][i]?.getD 0
theorem rotationDot_28_13_checked : rotationDot_28_13.ExtendedCheck nodes 3 := by decide
def rotationDot_28_14 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_28_14_checked : rotationDot_28_14.ExtendedCheck nodes 3 := by decide
def rotationDot_28_15 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,11,2430][i]?.getD 0
  accumulator := fun i => #[11,11,11,2430][i]?.getD 0
theorem rotationDot_28_15_checked : rotationDot_28_15.ExtendedCheck nodes 3 := by decide
def rotationDot_28_16 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2419,11,11][i]?.getD 0
  accumulator := fun i => #[11,2419,2419,2419][i]?.getD 0
theorem rotationDot_28_16_checked : rotationDot_28_16.ExtendedCheck nodes 3 := by decide
def rotationDot_28_17 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2433,11,11][i]?.getD 0
  accumulator := fun i => #[11,2433,2433,2433][i]?.getD 0
theorem rotationDot_28_17_checked : rotationDot_28_17.ExtendedCheck nodes 3 := by decide
def rotationDot_28_18 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2435][i]?.getD 0
  accumulator := fun i => #[11,11,11,2435][i]?.getD 0
theorem rotationDot_28_18_checked : rotationDot_28_18.ExtendedCheck nodes 3 := by decide
def rotationDot_28_19 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,403][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2438][i]?.getD 0
theorem rotationDot_28_19_checked : rotationDot_28_19.ExtendedCheck nodes 3 := by decide
def rotationDot_28_20 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_28_20_checked : rotationDot_28_20.ExtendedCheck nodes 3 := by decide
def rotationDot_28_21 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,11,2435][i]?.getD 0
  accumulator := fun i => #[11,11,11,2435][i]?.getD 0
theorem rotationDot_28_21_checked : rotationDot_28_21.ExtendedCheck nodes 3 := by decide
def rotationDot_28_22 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,2435][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2443][i]?.getD 0
theorem rotationDot_28_22_checked : rotationDot_28_22.ExtendedCheck nodes 3 := by decide
def rotationDot_28_23 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2440,11,11][i]?.getD 0
  accumulator := fun i => #[11,2440,2440,2440][i]?.getD 0
theorem rotationDot_28_23_checked : rotationDot_28_23.ExtendedCheck nodes 3 := by decide
def rotationDot_28_24 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2446][i]?.getD 0
  accumulator := fun i => #[11,11,11,2446][i]?.getD 0
theorem rotationDot_28_24_checked : rotationDot_28_24.ExtendedCheck nodes 3 := by decide
def rotationDot_28_25 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2437,11,2435][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2443][i]?.getD 0
theorem rotationDot_28_25_checked : rotationDot_28_25.ExtendedCheck nodes 3 := by decide
def rotationDot_28_26 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_28_26_checked : rotationDot_28_26.ExtendedCheck nodes 3 := by decide
def rotationDot_28_27 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,11,2446][i]?.getD 0
  accumulator := fun i => #[11,11,11,2446][i]?.getD 0
theorem rotationDot_28_27_checked : rotationDot_28_27.ExtendedCheck nodes 3 := by decide
def rotationDot_28_28 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2437,11,403][i]?.getD 0
  accumulator := fun i => #[11,2437,2437,2438][i]?.getD 0
theorem rotationDot_28_28_checked : rotationDot_28_28.ExtendedCheck nodes 3 := by decide
def rotationDot_28_29 : DotRecipe where
  left := fun i => #[1048,11,10][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[2449,11,11][i]?.getD 0
  accumulator := fun i => #[11,2449,2449,2449][i]?.getD 0
theorem rotationDot_28_29_checked : rotationDot_28_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow28 : Array DotRecipe := #[rotationDot_28_0,rotationDot_28_1,rotationDot_28_2,rotationDot_28_3,rotationDot_28_4,rotationDot_28_5,rotationDot_28_6,rotationDot_28_7,rotationDot_28_8,rotationDot_28_9,rotationDot_28_10,rotationDot_28_11,rotationDot_28_12,rotationDot_28_13,rotationDot_28_14,rotationDot_28_15,rotationDot_28_16,rotationDot_28_17,rotationDot_28_18,rotationDot_28_19,rotationDot_28_20,rotationDot_28_21,rotationDot_28_22,rotationDot_28_23,rotationDot_28_24,rotationDot_28_25,rotationDot_28_26,rotationDot_28_27,rotationDot_28_28,rotationDot_28_29]
theorem rotationDotsRow28_checked (j : Fin 30) :
    (rotationDotsRow28[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_28_0_checked
  · exact rotationDot_28_1_checked
  · exact rotationDot_28_2_checked
  · exact rotationDot_28_3_checked
  · exact rotationDot_28_4_checked
  · exact rotationDot_28_5_checked
  · exact rotationDot_28_6_checked
  · exact rotationDot_28_7_checked
  · exact rotationDot_28_8_checked
  · exact rotationDot_28_9_checked
  · exact rotationDot_28_10_checked
  · exact rotationDot_28_11_checked
  · exact rotationDot_28_12_checked
  · exact rotationDot_28_13_checked
  · exact rotationDot_28_14_checked
  · exact rotationDot_28_15_checked
  · exact rotationDot_28_16_checked
  · exact rotationDot_28_17_checked
  · exact rotationDot_28_18_checked
  · exact rotationDot_28_19_checked
  · exact rotationDot_28_20_checked
  · exact rotationDot_28_21_checked
  · exact rotationDot_28_22_checked
  · exact rotationDot_28_23_checked
  · exact rotationDot_28_24_checked
  · exact rotationDot_28_25_checked
  · exact rotationDot_28_26_checked
  · exact rotationDot_28_27_checked
  · exact rotationDot_28_28_checked
  · exact rotationDot_28_29_checked
def rotationDot_29_0 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,2,11][i]?.getD 0
  product := fun i => #[11,14,11][i]?.getD 0
  accumulator := fun i => #[11,11,14,14][i]?.getD 0
theorem rotationDot_29_0_checked : rotationDot_29_0.ExtendedCheck nodes 3 := by decide
def rotationDot_29_1 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[15,11,11][i]?.getD 0
  product := fun i => #[2457,11,11][i]?.getD 0
  accumulator := fun i => #[11,2457,2457,2457][i]?.getD 0
theorem rotationDot_29_1_checked : rotationDot_29_1.ExtendedCheck nodes 3 := by decide
def rotationDot_29_2 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_29_2_checked : rotationDot_29_2.ExtendedCheck nodes 3 := by decide
def rotationDot_29_3 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,15,11][i]?.getD 0
  product := fun i => #[11,2457,11][i]?.getD 0
  accumulator := fun i => #[11,11,2457,2457][i]?.getD 0
theorem rotationDot_29_3_checked : rotationDot_29_3.ExtendedCheck nodes 3 := by decide
def rotationDot_29_4 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[2,11,11][i]?.getD 0
  product := fun i => #[14,11,11][i]?.getD 0
  accumulator := fun i => #[11,14,14,14][i]?.getD 0
theorem rotationDot_29_4_checked : rotationDot_29_4.ExtendedCheck nodes 3 := by decide
def rotationDot_29_5 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,11,11][i]?.getD 0
  product := fun i => #[11,11,11][i]?.getD 0
  accumulator := fun i => #[11,11,11,11][i]?.getD 0
theorem rotationDot_29_5_checked : rotationDot_29_5.ExtendedCheck nodes 3 := by decide
def rotationDot_29_6 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_29_6_checked : rotationDot_29_6.ExtendedCheck nodes 3 := by decide
def rotationDot_29_7 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[12,11,5][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_29_7_checked : rotationDot_29_7.ExtendedCheck nodes 3 := by decide
def rotationDot_29_8 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,13,11][i]?.getD 0
  product := fun i => #[11,2390,11][i]?.getD 0
  accumulator := fun i => #[11,11,2390,2390][i]?.getD 0
theorem rotationDot_29_8_checked : rotationDot_29_8.ExtendedCheck nodes 3 := by decide
def rotationDot_29_9 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,0,13][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_29_9_checked : rotationDot_29_9.ExtendedCheck nodes 3 := by decide
def rotationDot_29_10 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_29_10_checked : rotationDot_29_10.ExtendedCheck nodes 3 := by decide
def rotationDot_29_11 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[5,11,11][i]?.getD 0
  product := fun i => #[2387,11,11][i]?.getD 0
  accumulator := fun i => #[11,2387,2387,2387][i]?.getD 0
theorem rotationDot_29_11_checked : rotationDot_29_11.ExtendedCheck nodes 3 := by decide
def rotationDot_29_12 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,0,11][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_29_12_checked : rotationDot_29_12.ExtendedCheck nodes 3 := by decide
def rotationDot_29_13 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[12,11,13][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_29_13_checked : rotationDot_29_13.ExtendedCheck nodes 3 := by decide
def rotationDot_29_14 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,345,11][i]?.getD 0
  product := fun i => #[11,2397,11][i]?.getD 0
  accumulator := fun i => #[11,11,2397,2397][i]?.getD 0
theorem rotationDot_29_14_checked : rotationDot_29_14.ExtendedCheck nodes 3 := by decide
def rotationDot_29_15 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,0,345][i]?.getD 0
  product := fun i => #[11,2460,11][i]?.getD 0
  accumulator := fun i => #[11,11,2460,2460][i]?.getD 0
theorem rotationDot_29_15_checked : rotationDot_29_15.ExtendedCheck nodes 3 := by decide
def rotationDot_29_16 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[12,11,11][i]?.getD 0
  product := fun i => #[2474,11,11][i]?.getD 0
  accumulator := fun i => #[11,2474,2474,2474][i]?.getD 0
theorem rotationDot_29_16_checked : rotationDot_29_16.ExtendedCheck nodes 3 := by decide
def rotationDot_29_17 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[13,11,11][i]?.getD 0
  product := fun i => #[2390,11,11][i]?.getD 0
  accumulator := fun i => #[11,2390,2390,2390][i]?.getD 0
theorem rotationDot_29_17_checked : rotationDot_29_17.ExtendedCheck nodes 3 := by decide
def rotationDot_29_18 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_29_18_checked : rotationDot_29_18.ExtendedCheck nodes 3 := by decide
def rotationDot_29_19 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_29_19_checked : rotationDot_29_19.ExtendedCheck nodes 3 := by decide
def rotationDot_29_20 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[10,14,11][i]?.getD 0
  product := fun i => #[2402,710,11][i]?.getD 0
  accumulator := fun i => #[11,2402,2705,2705][i]?.getD 0
theorem rotationDot_29_20_checked : rotationDot_29_20.ExtendedCheck nodes 3 := by decide
def rotationDot_29_21 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,12,14][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_29_21_checked : rotationDot_29_21.ExtendedCheck nodes 3 := by decide
def rotationDot_29_22 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_29_22_checked : rotationDot_29_22.ExtendedCheck nodes 3 := by decide
def rotationDot_29_23 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[10,1461,11][i]?.getD 0
  product := fun i => #[2402,2409,11][i]?.getD 0
  accumulator := fun i => #[11,2402,2709,2709][i]?.getD 0
theorem rotationDot_29_23_checked : rotationDot_29_23.ExtendedCheck nodes 3 := by decide
def rotationDot_29_24 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_29_24_checked : rotationDot_29_24.ExtendedCheck nodes 3 := by decide
def rotationDot_29_25 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[1048,11,14][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_29_25_checked : rotationDot_29_25.ExtendedCheck nodes 3 := by decide
def rotationDot_29_26 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[14,1461,11][i]?.getD 0
  product := fun i => #[710,2409,11][i]?.getD 0
  accumulator := fun i => #[11,710,2712,2712][i]?.getD 0
theorem rotationDot_29_26_checked : rotationDot_29_26.ExtendedCheck nodes 3 := by decide
def rotationDot_29_27 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[11,12,1461][i]?.getD 0
  product := fun i => #[11,2474,11][i]?.getD 0
  accumulator := fun i => #[11,11,2474,2474][i]?.getD 0
theorem rotationDot_29_27_checked : rotationDot_29_27.ExtendedCheck nodes 3 := by decide
def rotationDot_29_28 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[1048,11,10][i]?.getD 0
  product := fun i => #[2635,11,11][i]?.getD 0
  accumulator := fun i => #[11,2635,2635,2635][i]?.getD 0
theorem rotationDot_29_28_checked : rotationDot_29_28.ExtendedCheck nodes 3 := by decide
def rotationDot_29_29 : DotRecipe where
  left := fun i => #[14,14,11][i]?.getD 0
  right := fun i => #[14,14,11][i]?.getD 0
  product := fun i => #[710,710,11][i]?.getD 0
  accumulator := fun i => #[11,710,1110,1110][i]?.getD 0
theorem rotationDot_29_29_checked : rotationDot_29_29.ExtendedCheck nodes 3 := by decide
def rotationDotsRow29 : Array DotRecipe := #[rotationDot_29_0,rotationDot_29_1,rotationDot_29_2,rotationDot_29_3,rotationDot_29_4,rotationDot_29_5,rotationDot_29_6,rotationDot_29_7,rotationDot_29_8,rotationDot_29_9,rotationDot_29_10,rotationDot_29_11,rotationDot_29_12,rotationDot_29_13,rotationDot_29_14,rotationDot_29_15,rotationDot_29_16,rotationDot_29_17,rotationDot_29_18,rotationDot_29_19,rotationDot_29_20,rotationDot_29_21,rotationDot_29_22,rotationDot_29_23,rotationDot_29_24,rotationDot_29_25,rotationDot_29_26,rotationDot_29_27,rotationDot_29_28,rotationDot_29_29]
theorem rotationDotsRow29_checked (j : Fin 30) :
    (rotationDotsRow29[j.val]?.getD rotationDot_0_0).ExtendedCheck nodes 3 := by
  fin_cases j
  · exact rotationDot_29_0_checked
  · exact rotationDot_29_1_checked
  · exact rotationDot_29_2_checked
  · exact rotationDot_29_3_checked
  · exact rotationDot_29_4_checked
  · exact rotationDot_29_5_checked
  · exact rotationDot_29_6_checked
  · exact rotationDot_29_7_checked
  · exact rotationDot_29_8_checked
  · exact rotationDot_29_9_checked
  · exact rotationDot_29_10_checked
  · exact rotationDot_29_11_checked
  · exact rotationDot_29_12_checked
  · exact rotationDot_29_13_checked
  · exact rotationDot_29_14_checked
  · exact rotationDot_29_15_checked
  · exact rotationDot_29_16_checked
  · exact rotationDot_29_17_checked
  · exact rotationDot_29_18_checked
  · exact rotationDot_29_19_checked
  · exact rotationDot_29_20_checked
  · exact rotationDot_29_21_checked
  · exact rotationDot_29_22_checked
  · exact rotationDot_29_23_checked
  · exact rotationDot_29_24_checked
  · exact rotationDot_29_25_checked
  · exact rotationDot_29_26_checked
  · exact rotationDot_29_27_checked
  · exact rotationDot_29_28_checked
  · exact rotationDot_29_29_checked
def rotationDots (ia jb : Fin 10 × Fin 3) : DotRecipe :=
  (#[rotationDotsRow0,rotationDotsRow1,rotationDotsRow2,rotationDotsRow3,rotationDotsRow4,rotationDotsRow5,rotationDotsRow6,rotationDotsRow7,rotationDotsRow8,rotationDotsRow9,rotationDotsRow10,rotationDotsRow11,rotationDotsRow12,rotationDotsRow13,rotationDotsRow14,rotationDotsRow15,rotationDotsRow16,rotationDotsRow17,rotationDotsRow18,rotationDotsRow19,rotationDotsRow20,rotationDotsRow21,rotationDotsRow22,rotationDotsRow23,rotationDotsRow24,rotationDotsRow25,rotationDotsRow26,rotationDotsRow27,rotationDotsRow28,rotationDotsRow29][flatIndex ia]?.getD #[])[flatIndex jb]?.getD rotationDot_0_0
theorem rotation_dots_checked (ia jb : Fin 10 × Fin 3) : (rotationDots ia jb).ExtendedCheck nodes 3 := by
  rcases ia with ⟨i,a⟩
  have hj : flatIndex jb < 30 := by rcases jb with ⟨j,b⟩; simp only [flatIndex]; omega
  fin_cases i <;> fin_cases a
  · exact rotationDotsRow0_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow1_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow2_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow3_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow4_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow5_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow6_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow7_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow8_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow9_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow10_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow11_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow12_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow13_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow14_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow15_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow16_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow17_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow18_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow19_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow20_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow21_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow22_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow23_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow24_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow25_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow26_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow27_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow28_checked ⟨flatIndex jb,hj⟩
  · exact rotationDotsRow29_checked ⟨flatIndex jb,hj⟩
theorem rotation_dot_left (ia jb : Fin 10 × Fin 3) (k : Fin 3) :
    (rotationDots ia jb).left k = rotationIndices ia.1 ia.2 k := by revert ia jb k; decide
theorem rotation_dot_right (ia jb : Fin 10 × Fin 3) (k : Fin 3) :
    (rotationDots ia jb).right k = rotationIndices jb.1 jb.2 k := by revert ia jb k; decide
theorem rotation_product_sound (r : ℝ) (ia jb : Fin 10 × Fin 3) :
    value (parameterInputs r) nodes ((rotationDots ia jb).accumulator 3) =
      (rotationColumns (candidateAt r)*(rotationColumns (candidateAt r)).transpose) ia jb := by
  rw [DotRecipe.extended_sound_fin _ _ _ _ (rotation_dots_checked ia jb)]
  simp only [rotation_dot_left, rotation_dot_right, rotation_entry_sound, Matrix.mul_apply, Matrix.transpose_apply]
theorem augmented_checked (ia jb : Fin 10 × Fin 3) :
    ExtendedSmartAddCheck nodes (constrainedIndices (flatIndex ia) (flatIndex jb))
      ((rotationDots ia jb).accumulator 3)
      (augmentedIndices (flatIndex ia) (flatIndex jb)) := by revert ia jb; decide
theorem shifted_checked (ia jb : Fin 10 × Fin 3) :
    ExtendedSmartAddCheck nodes (augmentedIndices (flatIndex ia) (flatIndex jb))
      (if ia = jb then negativeShift else 11)
      (hessianIndices (flatIndex ia) (flatIndex jb)) := by revert ia jb; decide
theorem negative_shift_sound (values : ℕ → ℝ) : value values nodes negativeShift = -(1/20 : ℝ) := by
  simpa [neg_div] using value_constant values nodes negativeShift (-1) 20 (by decide)
theorem shifted_hessian_entry_sound (r : ℝ) (ia jb : Fin 10 × Fin 3) :
    value (parameterInputs r) nodes (hessianIndices (flatIndex ia) (flatIndex jb)) =
      (constrainedHessian (candidateAt r) +
        rotationColumns (candidateAt r)*(rotationColumns (candidateAt r)).transpose -
          (1/20 : ℝ) • (1 : Matrix (Fin 10 × Fin 3) (Fin 10 × Fin 3) ℝ)) ia jb := by
  rw [extendedSmartAdd_sound _ _ _ _ _ (shifted_checked ia jb),
    extendedSmartAdd_sound _ _ _ _ _ (augmented_checked ia jb),
    constrained_entry_sound, rotation_product_sound]
  by_cases hij : ia = jb
  · subst jb
    rw [if_pos rfl, negative_shift_sound]
    simp [Matrix.sub_apply, Matrix.add_apply, sub_eq_add_neg]
  · rw [if_neg hij, literal_zero]
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, hij]
#print axioms laplacian_entry_sound
#print axioms radial_entry_sound
#print axioms shifted_hessian_entry_sound
end ThomsonN10.Local.Certificates.AmbientKernel

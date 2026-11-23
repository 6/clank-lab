import RupPieces
import PublishedInput
open Std.Sat RupPieces
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
private def c1 : CNF.Clause Nat := [(0, true), (1, true), (2, true)]
private def c2 : CNF.Clause Nat := [(0, false), (1, false)]
private def c3 : CNF.Clause Nat := [(0, false), (2, false)]
private def c4 : CNF.Clause Nat := [(1, false), (2, false)]
private def c5 : CNF.Clause Nat := [(3, true), (4, true), (5, true)]
private def c6 : CNF.Clause Nat := [(3, false), (4, false)]
private def c7 : CNF.Clause Nat := [(3, false), (5, false)]
private def c8 : CNF.Clause Nat := [(4, false), (5, false)]
private def c9 : CNF.Clause Nat := [(6, true), (7, true), (8, true)]
private def c10 : CNF.Clause Nat := [(6, false), (7, false)]
private def c11 : CNF.Clause Nat := [(6, false), (8, false)]
private def c12 : CNF.Clause Nat := [(7, false), (8, false)]
private def c13 : CNF.Clause Nat := [(9, true), (10, true), (11, true)]
private def c14 : CNF.Clause Nat := [(9, false), (10, false)]
private def c15 : CNF.Clause Nat := [(9, false), (11, false)]
private def c16 : CNF.Clause Nat := [(10, false), (11, false)]
private def c17 : CNF.Clause Nat := [(12, true), (13, true), (14, true)]
private def c18 : CNF.Clause Nat := [(12, false), (13, false)]
private def c19 : CNF.Clause Nat := [(12, false), (14, false)]
private def c20 : CNF.Clause Nat := [(13, false), (14, false)]
private def c21 : CNF.Clause Nat := [(15, true), (16, true), (17, true)]
private def c22 : CNF.Clause Nat := [(15, false), (16, false)]
private def c23 : CNF.Clause Nat := [(15, false), (17, false)]
private def c24 : CNF.Clause Nat := [(16, false), (17, false)]
private def c25 : CNF.Clause Nat := [(18, true), (19, true), (20, true)]
private def c26 : CNF.Clause Nat := [(18, false), (19, false)]
private def c27 : CNF.Clause Nat := [(18, false), (20, false)]
private def c28 : CNF.Clause Nat := [(19, false), (20, false)]
private def c29 : CNF.Clause Nat := [(21, true), (22, true), (23, true)]
private def c30 : CNF.Clause Nat := [(21, false), (22, false)]
private def c31 : CNF.Clause Nat := [(21, false), (23, false)]
private def c32 : CNF.Clause Nat := [(22, false), (23, false)]
private def c33 : CNF.Clause Nat := [(24, true), (25, true), (26, true)]
private def c34 : CNF.Clause Nat := [(24, false), (25, false)]
private def c35 : CNF.Clause Nat := [(24, false), (26, false)]
private def c36 : CNF.Clause Nat := [(25, false), (26, false)]
private def c37 : CNF.Clause Nat := [(27, true), (28, true), (29, true)]
private def c38 : CNF.Clause Nat := [(27, false), (28, false)]
private def c39 : CNF.Clause Nat := [(27, false), (29, false)]
private def c40 : CNF.Clause Nat := [(28, false), (29, false)]
private def c41 : CNF.Clause Nat := [(30, true), (31, true), (32, true)]
private def c42 : CNF.Clause Nat := [(30, false), (31, false)]
private def c43 : CNF.Clause Nat := [(30, false), (32, false)]
private def c44 : CNF.Clause Nat := [(31, false), (32, false)]
private def c45 : CNF.Clause Nat := [(33, true), (34, true), (35, true)]
private def c46 : CNF.Clause Nat := [(33, false), (34, false)]
private def c47 : CNF.Clause Nat := [(33, false), (35, false)]
private def c48 : CNF.Clause Nat := [(34, false), (35, false)]
private def c49 : CNF.Clause Nat := [(36, true), (37, true), (38, true)]
private def c50 : CNF.Clause Nat := [(36, false), (37, false)]
private def c51 : CNF.Clause Nat := [(36, false), (38, false)]
private def c52 : CNF.Clause Nat := [(37, false), (38, false)]
private def c53 : CNF.Clause Nat := [(39, true), (40, true), (41, true)]
private def c54 : CNF.Clause Nat := [(39, false), (40, false)]
private def c55 : CNF.Clause Nat := [(39, false), (41, false)]
private def c56 : CNF.Clause Nat := [(40, false), (41, false)]
private def c57 : CNF.Clause Nat := [(42, true), (43, true), (44, true)]
private def c58 : CNF.Clause Nat := [(42, false), (43, false)]
private def c59 : CNF.Clause Nat := [(42, false), (44, false)]
private def c60 : CNF.Clause Nat := [(43, false), (44, false)]
private def c61 : CNF.Clause Nat := [(45, true), (46, true), (47, true)]
private def c62 : CNF.Clause Nat := [(45, false), (46, false)]
private def c63 : CNF.Clause Nat := [(45, false), (47, false)]
private def c64 : CNF.Clause Nat := [(46, false), (47, false)]
private def c65 : CNF.Clause Nat := [(48, true), (49, true), (50, true)]
private def c66 : CNF.Clause Nat := [(48, false), (49, false)]
private def c67 : CNF.Clause Nat := [(48, false), (50, false)]
private def c68 : CNF.Clause Nat := [(49, false), (50, false)]
private def c69 : CNF.Clause Nat := [(51, true), (52, true), (53, true)]
private def c70 : CNF.Clause Nat := [(51, false), (52, false)]
private def c71 : CNF.Clause Nat := [(51, false), (53, false)]
private def c72 : CNF.Clause Nat := [(52, false), (53, false)]
private def c73 : CNF.Clause Nat := [(54, true), (55, true), (56, true)]
private def c74 : CNF.Clause Nat := [(54, false), (55, false)]
private def c75 : CNF.Clause Nat := [(54, false), (56, false)]
private def c76 : CNF.Clause Nat := [(55, false), (56, false)]
private def c77 : CNF.Clause Nat := [(57, true), (58, true), (59, true)]
private def c78 : CNF.Clause Nat := [(57, false), (58, false)]
private def c79 : CNF.Clause Nat := [(57, false), (59, false)]
private def c80 : CNF.Clause Nat := [(58, false), (59, false)]
private def c81 : CNF.Clause Nat := [(60, true), (61, true), (62, true)]
private def c82 : CNF.Clause Nat := [(60, false), (61, false)]
private def c83 : CNF.Clause Nat := [(60, false), (62, false)]
private def c84 : CNF.Clause Nat := [(61, false), (62, false)]
private def c85 : CNF.Clause Nat := [(63, true), (64, true), (65, true)]
private def c86 : CNF.Clause Nat := [(63, false), (64, false)]
private def c87 : CNF.Clause Nat := [(63, false), (65, false)]
private def c88 : CNF.Clause Nat := [(64, false), (65, false)]
private def c89 : CNF.Clause Nat := [(66, true), (67, true), (68, true)]
private def c90 : CNF.Clause Nat := [(66, false), (67, false)]
private def c91 : CNF.Clause Nat := [(66, false), (68, false)]
private def c92 : CNF.Clause Nat := [(67, false), (68, false)]
private def c93 : CNF.Clause Nat := [(69, true), (70, true), (71, true)]
private def c94 : CNF.Clause Nat := [(69, false), (70, false)]
private def c95 : CNF.Clause Nat := [(69, false), (71, false)]
private def c96 : CNF.Clause Nat := [(70, false), (71, false)]
private def c97 : CNF.Clause Nat := [(72, true), (73, true), (74, true)]
private def c98 : CNF.Clause Nat := [(72, false), (73, false)]
private def c99 : CNF.Clause Nat := [(72, false), (74, false)]
private def c100 : CNF.Clause Nat := [(73, false), (74, false)]
private def c101 : CNF.Clause Nat := [(75, true), (76, true), (77, true)]
private def c102 : CNF.Clause Nat := [(75, false), (76, false)]
private def c103 : CNF.Clause Nat := [(75, false), (77, false)]
private def c104 : CNF.Clause Nat := [(76, false), (77, false)]
private def c105 : CNF.Clause Nat := [(78, true), (79, true), (80, true)]
private def c106 : CNF.Clause Nat := [(78, false), (79, false)]
private def c107 : CNF.Clause Nat := [(78, false), (80, false)]
private def c108 : CNF.Clause Nat := [(79, false), (80, false)]
private def c109 : CNF.Clause Nat := [(81, true), (82, true), (83, true)]
private def c110 : CNF.Clause Nat := [(81, false), (82, false)]
private def c111 : CNF.Clause Nat := [(81, false), (83, false)]
private def c112 : CNF.Clause Nat := [(82, false), (83, false)]
private def c113 : CNF.Clause Nat := [(84, true), (85, true), (86, true)]
private def c114 : CNF.Clause Nat := [(84, false), (85, false)]
private def c115 : CNF.Clause Nat := [(84, false), (86, false)]
private def c116 : CNF.Clause Nat := [(85, false), (86, false)]
private def c117 : CNF.Clause Nat := [(87, true), (88, true), (89, true)]
private def c118 : CNF.Clause Nat := [(87, false), (88, false)]
private def c119 : CNF.Clause Nat := [(87, false), (89, false)]
private def c120 : CNF.Clause Nat := [(88, false), (89, false)]
private def c121 : CNF.Clause Nat := [(90, true), (91, true), (92, true)]
private def c122 : CNF.Clause Nat := [(90, false), (91, false)]
private def c123 : CNF.Clause Nat := [(90, false), (92, false)]
private def c124 : CNF.Clause Nat := [(91, false), (92, false)]
private def c125 : CNF.Clause Nat := [(93, true), (94, true), (95, true)]
private def c126 : CNF.Clause Nat := [(93, false), (94, false)]
private def c127 : CNF.Clause Nat := [(93, false), (95, false)]
private def c128 : CNF.Clause Nat := [(94, false), (95, false)]
private def c129 : CNF.Clause Nat := [(96, true), (97, true), (98, true)]
private def c130 : CNF.Clause Nat := [(96, false), (97, false)]
private def c131 : CNF.Clause Nat := [(96, false), (98, false)]
private def c132 : CNF.Clause Nat := [(97, false), (98, false)]
private def c133 : CNF.Clause Nat := [(99, true), (100, true), (101, true)]
private def c134 : CNF.Clause Nat := [(99, false), (100, false)]
private def c135 : CNF.Clause Nat := [(99, false), (101, false)]
private def c136 : CNF.Clause Nat := [(100, false), (101, false)]
private def c137 : CNF.Clause Nat := [(102, true), (103, true), (104, true)]
private def c138 : CNF.Clause Nat := [(102, false), (103, false)]
private def c139 : CNF.Clause Nat := [(102, false), (104, false)]
private def c140 : CNF.Clause Nat := [(103, false), (104, false)]
private def c141 : CNF.Clause Nat := [(105, true), (106, true), (107, true)]
private def c142 : CNF.Clause Nat := [(105, false), (106, false)]
private def c143 : CNF.Clause Nat := [(105, false), (107, false)]
private def c144 : CNF.Clause Nat := [(106, false), (107, false)]
private def c145 : CNF.Clause Nat := [(108, true), (109, true), (110, true)]
private def c146 : CNF.Clause Nat := [(108, false), (109, false)]
private def c147 : CNF.Clause Nat := [(108, false), (110, false)]
private def c148 : CNF.Clause Nat := [(109, false), (110, false)]
private def c149 : CNF.Clause Nat := [(111, true), (112, true), (113, true)]
private def c150 : CNF.Clause Nat := [(111, false), (112, false)]
private def c151 : CNF.Clause Nat := [(111, false), (113, false)]
private def c152 : CNF.Clause Nat := [(112, false), (113, false)]
private def c153 : CNF.Clause Nat := [(114, true), (115, true), (116, true)]
private def c154 : CNF.Clause Nat := [(114, false), (115, false)]
private def c155 : CNF.Clause Nat := [(114, false), (116, false)]
private def c156 : CNF.Clause Nat := [(115, false), (116, false)]
private def c157 : CNF.Clause Nat := [(117, true), (118, true), (119, true)]
private def c158 : CNF.Clause Nat := [(117, false), (118, false)]
private def c159 : CNF.Clause Nat := [(117, false), (119, false)]
private def c160 : CNF.Clause Nat := [(118, false), (119, false)]
private def c161 : CNF.Clause Nat := [(120, true), (121, true), (122, true)]
private def c162 : CNF.Clause Nat := [(120, false), (121, false)]
private def c163 : CNF.Clause Nat := [(120, false), (122, false)]
private def c164 : CNF.Clause Nat := [(121, false), (122, false)]
private def c165 : CNF.Clause Nat := [(123, true), (124, true), (125, true)]
private def c166 : CNF.Clause Nat := [(123, false), (124, false)]
private def c167 : CNF.Clause Nat := [(123, false), (125, false)]
private def c168 : CNF.Clause Nat := [(124, false), (125, false)]
private def c169 : CNF.Clause Nat := [(126, true), (127, true), (128, true)]
private def c170 : CNF.Clause Nat := [(126, false), (127, false)]
private def c171 : CNF.Clause Nat := [(126, false), (128, false)]
private def c172 : CNF.Clause Nat := [(127, false), (128, false)]
private def c173 : CNF.Clause Nat := [(129, true), (130, true), (131, true)]
private def c174 : CNF.Clause Nat := [(129, false), (130, false)]
private def c175 : CNF.Clause Nat := [(129, false), (131, false)]
private def c176 : CNF.Clause Nat := [(130, false), (131, false)]
private def c177 : CNF.Clause Nat := [(132, true), (133, true), (134, true)]
private def c178 : CNF.Clause Nat := [(132, false), (133, false)]
private def c179 : CNF.Clause Nat := [(132, false), (134, false)]
private def c180 : CNF.Clause Nat := [(133, false), (134, false)]
private def c181 : CNF.Clause Nat := [(135, true), (136, true), (137, true)]
private def c182 : CNF.Clause Nat := [(135, false), (136, false)]
private def c183 : CNF.Clause Nat := [(135, false), (137, false)]
private def c184 : CNF.Clause Nat := [(136, false), (137, false)]
private def c185 : CNF.Clause Nat := [(138, true), (139, true), (140, true)]
private def c186 : CNF.Clause Nat := [(138, false), (139, false)]
private def c187 : CNF.Clause Nat := [(138, false), (140, false)]
private def c188 : CNF.Clause Nat := [(139, false), (140, false)]
private def c189 : CNF.Clause Nat := [(141, true), (142, true), (143, true)]
private def c190 : CNF.Clause Nat := [(141, false), (142, false)]
private def c191 : CNF.Clause Nat := [(141, false), (143, false)]
private def c192 : CNF.Clause Nat := [(142, false), (143, false)]
private def c193 : CNF.Clause Nat := [(144, true), (145, true), (146, true)]
private def c194 : CNF.Clause Nat := [(144, false), (145, false)]
private def c195 : CNF.Clause Nat := [(144, false), (146, false)]
private def c196 : CNF.Clause Nat := [(145, false), (146, false)]
private def c197 : CNF.Clause Nat := [(147, true), (148, true), (149, true)]
private def c198 : CNF.Clause Nat := [(147, false), (148, false)]
private def c199 : CNF.Clause Nat := [(147, false), (149, false)]
private def c200 : CNF.Clause Nat := [(148, false), (149, false)]
private def c201 : CNF.Clause Nat := [(150, true), (151, true), (152, true)]
private def c202 : CNF.Clause Nat := [(150, false), (151, false)]
private def c203 : CNF.Clause Nat := [(150, false), (152, false)]
private def c204 : CNF.Clause Nat := [(151, false), (152, false)]
private def c205 : CNF.Clause Nat := [(153, true), (154, true), (155, true)]
private def c206 : CNF.Clause Nat := [(153, false), (154, false)]
private def c207 : CNF.Clause Nat := [(153, false), (155, false)]
private def c208 : CNF.Clause Nat := [(154, false), (155, false)]
private def c209 : CNF.Clause Nat := [(156, true), (157, true), (158, true)]
private def c210 : CNF.Clause Nat := [(156, false), (157, false)]
private def c211 : CNF.Clause Nat := [(156, false), (158, false)]
private def c212 : CNF.Clause Nat := [(157, false), (158, false)]
private def c213 : CNF.Clause Nat := [(159, true), (160, true), (161, true)]
private def c214 : CNF.Clause Nat := [(159, false), (160, false)]
private def c215 : CNF.Clause Nat := [(159, false), (161, false)]
private def c216 : CNF.Clause Nat := [(160, false), (161, false)]
private def c217 : CNF.Clause Nat := [(162, true), (163, true), (164, true)]
private def c218 : CNF.Clause Nat := [(162, false), (163, false)]
private def c219 : CNF.Clause Nat := [(162, false), (164, false)]
private def c220 : CNF.Clause Nat := [(163, false), (164, false)]
private def c221 : CNF.Clause Nat := [(165, true), (166, true), (167, true)]
private def c222 : CNF.Clause Nat := [(165, false), (166, false)]
private def c223 : CNF.Clause Nat := [(165, false), (167, false)]
private def c224 : CNF.Clause Nat := [(166, false), (167, false)]
private def c225 : CNF.Clause Nat := [(168, true), (169, true), (170, true)]
private def c226 : CNF.Clause Nat := [(168, false), (169, false)]
private def c227 : CNF.Clause Nat := [(168, false), (170, false)]
private def c228 : CNF.Clause Nat := [(169, false), (170, false)]
private def c229 : CNF.Clause Nat := [(171, true), (172, true), (173, true)]
private def c230 : CNF.Clause Nat := [(171, false), (172, false)]
private def c231 : CNF.Clause Nat := [(171, false), (173, false)]
private def c232 : CNF.Clause Nat := [(172, false), (173, false)]
private def c233 : CNF.Clause Nat := [(174, true), (175, true), (176, true)]
private def c234 : CNF.Clause Nat := [(174, false), (175, false)]
private def c235 : CNF.Clause Nat := [(174, false), (176, false)]
private def c236 : CNF.Clause Nat := [(175, false), (176, false)]
private def c237 : CNF.Clause Nat := [(177, true), (178, true), (179, true)]
private def c238 : CNF.Clause Nat := [(177, false), (178, false)]
private def c239 : CNF.Clause Nat := [(177, false), (179, false)]
private def c240 : CNF.Clause Nat := [(178, false), (179, false)]
private def c241 : CNF.Clause Nat := [(180, true), (181, true), (182, true)]
private def c242 : CNF.Clause Nat := [(180, false), (181, false)]
private def c243 : CNF.Clause Nat := [(180, false), (182, false)]
private def c244 : CNF.Clause Nat := [(181, false), (182, false)]
private def c245 : CNF.Clause Nat := [(183, true), (184, true), (185, true)]
private def c246 : CNF.Clause Nat := [(183, false), (184, false)]
private def c247 : CNF.Clause Nat := [(183, false), (185, false)]
private def c248 : CNF.Clause Nat := [(184, false), (185, false)]
private def c249 : CNF.Clause Nat := [(186, true), (187, true), (188, true)]
private def c250 : CNF.Clause Nat := [(186, false), (187, false)]
private def c251 : CNF.Clause Nat := [(186, false), (188, false)]
private def c252 : CNF.Clause Nat := [(187, false), (188, false)]
private def c253 : CNF.Clause Nat := [(189, true), (190, true), (191, true)]
private def c254 : CNF.Clause Nat := [(189, false), (190, false)]
private def c255 : CNF.Clause Nat := [(189, false), (191, false)]
private def c256 : CNF.Clause Nat := [(190, false), (191, false)]
private def c257 : CNF.Clause Nat := [(192, true), (193, true), (194, true)]
private def c258 : CNF.Clause Nat := [(192, false), (193, false)]
private def c259 : CNF.Clause Nat := [(192, false), (194, false)]
private def c260 : CNF.Clause Nat := [(193, false), (194, false)]
private def c261 : CNF.Clause Nat := [(195, true), (196, true), (197, true)]
private def c262 : CNF.Clause Nat := [(195, false), (196, false)]
private def c263 : CNF.Clause Nat := [(195, false), (197, false)]
private def c264 : CNF.Clause Nat := [(196, false), (197, false)]
private def c265 : CNF.Clause Nat := [(198, true), (199, true), (200, true)]
private def c266 : CNF.Clause Nat := [(198, false), (199, false)]
private def c267 : CNF.Clause Nat := [(198, false), (200, false)]
private def c268 : CNF.Clause Nat := [(199, false), (200, false)]
private def c269 : CNF.Clause Nat := [(201, true), (202, true), (203, true)]
private def c270 : CNF.Clause Nat := [(201, false), (202, false)]
private def c271 : CNF.Clause Nat := [(201, false), (203, false)]
private def c272 : CNF.Clause Nat := [(202, false), (203, false)]
private def c273 : CNF.Clause Nat := [(204, true), (205, true), (206, true)]
private def c274 : CNF.Clause Nat := [(204, false), (205, false)]
private def c275 : CNF.Clause Nat := [(204, false), (206, false)]
private def c276 : CNF.Clause Nat := [(205, false), (206, false)]
private def c277 : CNF.Clause Nat := [(207, true), (208, true), (209, true)]
private def c278 : CNF.Clause Nat := [(207, false), (208, false)]
private def c279 : CNF.Clause Nat := [(207, false), (209, false)]
private def c280 : CNF.Clause Nat := [(208, false), (209, false)]
private def c281 : CNF.Clause Nat := [(210, true), (211, true), (212, true)]
private def c282 : CNF.Clause Nat := [(210, false), (211, false)]
private def c283 : CNF.Clause Nat := [(210, false), (212, false)]
private def c284 : CNF.Clause Nat := [(211, false), (212, false)]
private def c285 : CNF.Clause Nat := [(213, true), (214, true), (215, true)]
private def c286 : CNF.Clause Nat := [(213, false), (214, false)]
private def c287 : CNF.Clause Nat := [(213, false), (215, false)]
private def c288 : CNF.Clause Nat := [(214, false), (215, false)]
private def c289 : CNF.Clause Nat := [(216, true), (217, true), (218, true)]
private def c290 : CNF.Clause Nat := [(216, false), (217, false)]
private def c291 : CNF.Clause Nat := [(216, false), (218, false)]
private def c292 : CNF.Clause Nat := [(217, false), (218, false)]
private def c293 : CNF.Clause Nat := [(219, true), (220, true), (221, true)]
private def c294 : CNF.Clause Nat := [(219, false), (220, false)]
private def c295 : CNF.Clause Nat := [(219, false), (221, false)]
private def c296 : CNF.Clause Nat := [(220, false), (221, false)]
private def c297 : CNF.Clause Nat := [(222, true), (223, true), (224, true)]
private def c298 : CNF.Clause Nat := [(222, false), (223, false)]
private def c299 : CNF.Clause Nat := [(222, false), (224, false)]
private def c300 : CNF.Clause Nat := [(223, false), (224, false)]
private def c301 : CNF.Clause Nat := [(225, true), (226, true), (227, true)]
private def c302 : CNF.Clause Nat := [(225, false), (226, false)]
private def c303 : CNF.Clause Nat := [(225, false), (227, false)]
private def c304 : CNF.Clause Nat := [(226, false), (227, false)]
private def c305 : CNF.Clause Nat := [(228, true), (229, true), (230, true)]
private def c306 : CNF.Clause Nat := [(228, false), (229, false)]
private def c307 : CNF.Clause Nat := [(228, false), (230, false)]
private def c308 : CNF.Clause Nat := [(229, false), (230, false)]
private def c309 : CNF.Clause Nat := [(231, true), (232, true), (233, true)]
private def c310 : CNF.Clause Nat := [(231, false), (232, false)]
private def c311 : CNF.Clause Nat := [(231, false), (233, false)]
private def c312 : CNF.Clause Nat := [(232, false), (233, false)]
private def c313 : CNF.Clause Nat := [(234, true), (235, true), (236, true)]
private def c314 : CNF.Clause Nat := [(234, false), (235, false)]
private def c315 : CNF.Clause Nat := [(234, false), (236, false)]
private def c316 : CNF.Clause Nat := [(235, false), (236, false)]
private def c317 : CNF.Clause Nat := [(237, true), (238, true), (239, true)]
private def c318 : CNF.Clause Nat := [(237, false), (238, false)]
private def c319 : CNF.Clause Nat := [(237, false), (239, false)]
private def c320 : CNF.Clause Nat := [(238, false), (239, false)]
private def c321 : CNF.Clause Nat := [(240, true), (241, true), (242, true)]
private def c322 : CNF.Clause Nat := [(240, false), (241, false)]
private def c323 : CNF.Clause Nat := [(240, false), (242, false)]
private def c324 : CNF.Clause Nat := [(241, false), (242, false)]
private def c325 : CNF.Clause Nat := [(243, true), (244, true), (245, true)]
private def c326 : CNF.Clause Nat := [(243, false), (244, false)]
private def c327 : CNF.Clause Nat := [(243, false), (245, false)]
private def c328 : CNF.Clause Nat := [(244, false), (245, false)]
private def c329 : CNF.Clause Nat := [(0, false), (3, false)]
private def c330 : CNF.Clause Nat := [(1, false), (4, false)]
private def c331 : CNF.Clause Nat := [(2, false), (5, false)]
private def c332 : CNF.Clause Nat := [(0, false), (6, false)]
private def c333 : CNF.Clause Nat := [(1, false), (7, false)]
private def c334 : CNF.Clause Nat := [(2, false), (8, false)]
private def c335 : CNF.Clause Nat := [(0, false), (9, false)]
private def c336 : CNF.Clause Nat := [(1, false), (10, false)]
private def c337 : CNF.Clause Nat := [(2, false), (11, false)]
private def c338 : CNF.Clause Nat := [(0, false), (12, false)]
private def c339 : CNF.Clause Nat := [(1, false), (13, false)]
private def c340 : CNF.Clause Nat := [(2, false), (14, false)]
private def c341 : CNF.Clause Nat := [(0, false), (15, false)]
private def c342 : CNF.Clause Nat := [(1, false), (16, false)]
private def c343 : CNF.Clause Nat := [(2, false), (17, false)]
private def c344 : CNF.Clause Nat := [(0, false), (18, false)]
private def c345 : CNF.Clause Nat := [(1, false), (19, false)]
private def c346 : CNF.Clause Nat := [(2, false), (20, false)]
private def c347 : CNF.Clause Nat := [(3, false), (18, false)]
private def c348 : CNF.Clause Nat := [(4, false), (19, false)]
private def c349 : CNF.Clause Nat := [(5, false), (20, false)]
private def c350 : CNF.Clause Nat := [(3, false), (54, false)]
private def c351 : CNF.Clause Nat := [(4, false), (55, false)]
private def c352 : CNF.Clause Nat := [(5, false), (56, false)]
private def c353 : CNF.Clause Nat := [(3, false), (57, false)]
private def c354 : CNF.Clause Nat := [(4, false), (58, false)]
private def c355 : CNF.Clause Nat := [(5, false), (59, false)]
private def c356 : CNF.Clause Nat := [(3, false), (60, false)]
private def c357 : CNF.Clause Nat := [(4, false), (61, false)]
private def c358 : CNF.Clause Nat := [(5, false), (62, false)]
private def c359 : CNF.Clause Nat := [(3, false), (63, false)]
private def c360 : CNF.Clause Nat := [(4, false), (64, false)]
private def c361 : CNF.Clause Nat := [(5, false), (65, false)]
private def c362 : CNF.Clause Nat := [(6, false), (69, false)]
private def c363 : CNF.Clause Nat := [(7, false), (70, false)]
private def c364 : CNF.Clause Nat := [(8, false), (71, false)]
private def c365 : CNF.Clause Nat := [(6, false), (96, false)]
private def c366 : CNF.Clause Nat := [(7, false), (97, false)]
private def c367 : CNF.Clause Nat := [(8, false), (98, false)]
private def c368 : CNF.Clause Nat := [(9, false), (72, false)]
private def c369 : CNF.Clause Nat := [(10, false), (73, false)]
private def c370 : CNF.Clause Nat := [(11, false), (74, false)]
private def c371 : CNF.Clause Nat := [(9, false), (99, false)]
private def c372 : CNF.Clause Nat := [(10, false), (100, false)]
private def c373 : CNF.Clause Nat := [(11, false), (101, false)]
private def c374 : CNF.Clause Nat := [(12, false), (84, false)]
private def c375 : CNF.Clause Nat := [(13, false), (85, false)]
private def c376 : CNF.Clause Nat := [(14, false), (86, false)]
private def c377 : CNF.Clause Nat := [(12, false), (102, false)]
private def c378 : CNF.Clause Nat := [(13, false), (103, false)]
private def c379 : CNF.Clause Nat := [(14, false), (104, false)]
private def c380 : CNF.Clause Nat := [(15, false), (87, false)]
private def c381 : CNF.Clause Nat := [(16, false), (88, false)]
private def c382 : CNF.Clause Nat := [(17, false), (89, false)]
private def c383 : CNF.Clause Nat := [(15, false), (105, false)]
private def c384 : CNF.Clause Nat := [(16, false), (106, false)]
private def c385 : CNF.Clause Nat := [(17, false), (107, false)]
private def c386 : CNF.Clause Nat := [(18, false), (180, false)]
private def c387 : CNF.Clause Nat := [(19, false), (181, false)]
private def c388 : CNF.Clause Nat := [(20, false), (182, false)]
private def c389 : CNF.Clause Nat := [(18, false), (183, false)]
private def c390 : CNF.Clause Nat := [(19, false), (184, false)]
private def c391 : CNF.Clause Nat := [(20, false), (185, false)]
private def c392 : CNF.Clause Nat := [(21, false), (24, false)]
private def c393 : CNF.Clause Nat := [(22, false), (25, false)]
private def c394 : CNF.Clause Nat := [(23, false), (26, false)]
private def c395 : CNF.Clause Nat := [(21, false), (27, false)]
private def c396 : CNF.Clause Nat := [(22, false), (28, false)]
private def c397 : CNF.Clause Nat := [(23, false), (29, false)]
private def c398 : CNF.Clause Nat := [(21, false), (30, false)]
private def c399 : CNF.Clause Nat := [(22, false), (31, false)]
private def c400 : CNF.Clause Nat := [(23, false), (32, false)]
private def c401 : CNF.Clause Nat := [(21, false), (33, false)]
private def c402 : CNF.Clause Nat := [(22, false), (34, false)]
private def c403 : CNF.Clause Nat := [(23, false), (35, false)]
private def c404 : CNF.Clause Nat := [(21, false), (36, false)]
private def c405 : CNF.Clause Nat := [(22, false), (37, false)]
private def c406 : CNF.Clause Nat := [(23, false), (38, false)]
private def c407 : CNF.Clause Nat := [(21, false), (39, false)]
private def c408 : CNF.Clause Nat := [(22, false), (40, false)]
private def c409 : CNF.Clause Nat := [(23, false), (41, false)]
private def c410 : CNF.Clause Nat := [(21, false), (42, false)]
private def c411 : CNF.Clause Nat := [(22, false), (43, false)]
private def c412 : CNF.Clause Nat := [(23, false), (44, false)]
private def c413 : CNF.Clause Nat := [(21, false), (45, false)]
private def c414 : CNF.Clause Nat := [(22, false), (46, false)]
private def c415 : CNF.Clause Nat := [(23, false), (47, false)]
private def c416 : CNF.Clause Nat := [(21, false), (48, false)]
private def c417 : CNF.Clause Nat := [(22, false), (49, false)]
private def c418 : CNF.Clause Nat := [(23, false), (50, false)]
private def c419 : CNF.Clause Nat := [(21, false), (51, false)]
private def c420 : CNF.Clause Nat := [(22, false), (52, false)]
private def c421 : CNF.Clause Nat := [(23, false), (53, false)]
private def c422 : CNF.Clause Nat := [(24, false), (108, false)]
private def c423 : CNF.Clause Nat := [(25, false), (109, false)]
private def c424 : CNF.Clause Nat := [(26, false), (110, false)]
private def c425 : CNF.Clause Nat := [(24, false), (120, false)]
private def c426 : CNF.Clause Nat := [(25, false), (121, false)]
private def c427 : CNF.Clause Nat := [(26, false), (122, false)]
private def c428 : CNF.Clause Nat := [(27, false), (111, false)]
private def c429 : CNF.Clause Nat := [(28, false), (112, false)]
private def c430 : CNF.Clause Nat := [(29, false), (113, false)]
private def c431 : CNF.Clause Nat := [(27, false), (123, false)]
private def c432 : CNF.Clause Nat := [(28, false), (124, false)]
private def c433 : CNF.Clause Nat := [(29, false), (125, false)]
private def c434 : CNF.Clause Nat := [(30, false), (126, false)]
private def c435 : CNF.Clause Nat := [(31, false), (127, false)]
private def c436 : CNF.Clause Nat := [(32, false), (128, false)]
private def c437 : CNF.Clause Nat := [(30, false), (132, false)]
private def c438 : CNF.Clause Nat := [(31, false), (133, false)]
private def c439 : CNF.Clause Nat := [(32, false), (134, false)]
private def c440 : CNF.Clause Nat := [(33, false), (129, false)]
private def c441 : CNF.Clause Nat := [(34, false), (130, false)]
private def c442 : CNF.Clause Nat := [(35, false), (131, false)]
private def c443 : CNF.Clause Nat := [(33, false), (135, false)]
private def c444 : CNF.Clause Nat := [(34, false), (136, false)]
private def c445 : CNF.Clause Nat := [(35, false), (137, false)]
private def c446 : CNF.Clause Nat := [(36, false), (180, false)]
private def c447 : CNF.Clause Nat := [(37, false), (181, false)]
private def c448 : CNF.Clause Nat := [(38, false), (182, false)]
private def c449 : CNF.Clause Nat := [(36, false), (186, false)]
private def c450 : CNF.Clause Nat := [(37, false), (187, false)]
private def c451 : CNF.Clause Nat := [(38, false), (188, false)]
private def c452 : CNF.Clause Nat := [(39, false), (183, false)]
private def c453 : CNF.Clause Nat := [(40, false), (184, false)]
private def c454 : CNF.Clause Nat := [(41, false), (185, false)]
private def c455 : CNF.Clause Nat := [(39, false), (189, false)]
private def c456 : CNF.Clause Nat := [(40, false), (190, false)]
private def c457 : CNF.Clause Nat := [(41, false), (191, false)]
private def c458 : CNF.Clause Nat := [(42, false), (204, false)]
private def c459 : CNF.Clause Nat := [(43, false), (205, false)]
private def c460 : CNF.Clause Nat := [(44, false), (206, false)]
private def c461 : CNF.Clause Nat := [(42, false), (216, false)]
private def c462 : CNF.Clause Nat := [(43, false), (217, false)]
private def c463 : CNF.Clause Nat := [(44, false), (218, false)]
private def c464 : CNF.Clause Nat := [(45, false), (207, false)]
private def c465 : CNF.Clause Nat := [(46, false), (208, false)]
private def c466 : CNF.Clause Nat := [(47, false), (209, false)]
private def c467 : CNF.Clause Nat := [(45, false), (219, false)]
private def c468 : CNF.Clause Nat := [(46, false), (220, false)]
private def c469 : CNF.Clause Nat := [(47, false), (221, false)]
private def c470 : CNF.Clause Nat := [(48, false), (222, false)]
private def c471 : CNF.Clause Nat := [(49, false), (223, false)]
private def c472 : CNF.Clause Nat := [(50, false), (224, false)]
private def c473 : CNF.Clause Nat := [(48, false), (228, false)]
private def c474 : CNF.Clause Nat := [(49, false), (229, false)]
private def c475 : CNF.Clause Nat := [(50, false), (230, false)]
private def c476 : CNF.Clause Nat := [(51, false), (225, false)]
private def c477 : CNF.Clause Nat := [(52, false), (226, false)]
private def c478 : CNF.Clause Nat := [(53, false), (227, false)]
private def c479 : CNF.Clause Nat := [(51, false), (231, false)]
private def c480 : CNF.Clause Nat := [(52, false), (232, false)]
private def c481 : CNF.Clause Nat := [(53, false), (233, false)]
private def c482 : CNF.Clause Nat := [(54, false), (153, false)]
private def c483 : CNF.Clause Nat := [(55, false), (154, false)]
private def c484 : CNF.Clause Nat := [(56, false), (155, false)]
private def c485 : CNF.Clause Nat := [(54, false), (192, false)]
private def c486 : CNF.Clause Nat := [(55, false), (193, false)]
private def c487 : CNF.Clause Nat := [(56, false), (194, false)]
private def c488 : CNF.Clause Nat := [(57, false), (156, false)]
private def c489 : CNF.Clause Nat := [(58, false), (157, false)]
private def c490 : CNF.Clause Nat := [(59, false), (158, false)]
private def c491 : CNF.Clause Nat := [(57, false), (195, false)]
private def c492 : CNF.Clause Nat := [(58, false), (196, false)]
private def c493 : CNF.Clause Nat := [(59, false), (197, false)]
private def c494 : CNF.Clause Nat := [(60, false), (168, false)]
private def c495 : CNF.Clause Nat := [(61, false), (169, false)]
private def c496 : CNF.Clause Nat := [(62, false), (170, false)]
private def c497 : CNF.Clause Nat := [(60, false), (198, false)]
private def c498 : CNF.Clause Nat := [(61, false), (199, false)]
private def c499 : CNF.Clause Nat := [(62, false), (200, false)]
private def c500 : CNF.Clause Nat := [(63, false), (171, false)]
private def c501 : CNF.Clause Nat := [(64, false), (172, false)]
private def c502 : CNF.Clause Nat := [(65, false), (173, false)]
private def c503 : CNF.Clause Nat := [(63, false), (201, false)]
private def c504 : CNF.Clause Nat := [(64, false), (202, false)]
private def c505 : CNF.Clause Nat := [(65, false), (203, false)]
private def c506 : CNF.Clause Nat := [(66, false), (69, false)]
private def c507 : CNF.Clause Nat := [(67, false), (70, false)]
private def c508 : CNF.Clause Nat := [(68, false), (71, false)]
private def c509 : CNF.Clause Nat := [(66, false), (72, false)]
private def c510 : CNF.Clause Nat := [(67, false), (73, false)]
private def c511 : CNF.Clause Nat := [(68, false), (74, false)]
private def c512 : CNF.Clause Nat := [(66, false), (75, false)]
private def c513 : CNF.Clause Nat := [(67, false), (76, false)]
private def c514 : CNF.Clause Nat := [(68, false), (77, false)]
private def c515 : CNF.Clause Nat := [(66, false), (78, false)]
private def c516 : CNF.Clause Nat := [(67, false), (79, false)]
private def c517 : CNF.Clause Nat := [(68, false), (80, false)]
private def c518 : CNF.Clause Nat := [(69, false), (96, false)]
private def c519 : CNF.Clause Nat := [(70, false), (97, false)]
private def c520 : CNF.Clause Nat := [(71, false), (98, false)]
private def c521 : CNF.Clause Nat := [(72, false), (99, false)]
private def c522 : CNF.Clause Nat := [(73, false), (100, false)]
private def c523 : CNF.Clause Nat := [(74, false), (101, false)]
private def c524 : CNF.Clause Nat := [(75, false), (78, false)]
private def c525 : CNF.Clause Nat := [(76, false), (79, false)]
private def c526 : CNF.Clause Nat := [(77, false), (80, false)]
private def c527 : CNF.Clause Nat := [(75, false), (114, false)]
private def c528 : CNF.Clause Nat := [(76, false), (115, false)]
private def c529 : CNF.Clause Nat := [(77, false), (116, false)]
private def c530 : CNF.Clause Nat := [(75, false), (117, false)]
private def c531 : CNF.Clause Nat := [(76, false), (118, false)]
private def c532 : CNF.Clause Nat := [(77, false), (119, false)]
private def c533 : CNF.Clause Nat := [(78, false), (126, false)]
private def c534 : CNF.Clause Nat := [(79, false), (127, false)]
private def c535 : CNF.Clause Nat := [(80, false), (128, false)]
private def c536 : CNF.Clause Nat := [(78, false), (129, false)]
private def c537 : CNF.Clause Nat := [(79, false), (130, false)]
private def c538 : CNF.Clause Nat := [(80, false), (131, false)]
private def c539 : CNF.Clause Nat := [(81, false), (84, false)]
private def c540 : CNF.Clause Nat := [(82, false), (85, false)]
private def c541 : CNF.Clause Nat := [(83, false), (86, false)]
private def c542 : CNF.Clause Nat := [(81, false), (87, false)]
private def c543 : CNF.Clause Nat := [(82, false), (88, false)]
private def c544 : CNF.Clause Nat := [(83, false), (89, false)]
private def c545 : CNF.Clause Nat := [(81, false), (90, false)]
private def c546 : CNF.Clause Nat := [(82, false), (91, false)]
private def c547 : CNF.Clause Nat := [(83, false), (92, false)]
private def c548 : CNF.Clause Nat := [(81, false), (93, false)]
private def c549 : CNF.Clause Nat := [(82, false), (94, false)]
private def c550 : CNF.Clause Nat := [(83, false), (95, false)]
private def c551 : CNF.Clause Nat := [(84, false), (102, false)]
private def c552 : CNF.Clause Nat := [(85, false), (103, false)]
private def c553 : CNF.Clause Nat := [(86, false), (104, false)]
private def c554 : CNF.Clause Nat := [(87, false), (105, false)]
private def c555 : CNF.Clause Nat := [(88, false), (106, false)]
private def c556 : CNF.Clause Nat := [(89, false), (107, false)]
private def c557 : CNF.Clause Nat := [(90, false), (93, false)]
private def c558 : CNF.Clause Nat := [(91, false), (94, false)]
private def c559 : CNF.Clause Nat := [(92, false), (95, false)]
private def c560 : CNF.Clause Nat := [(90, false), (108, false)]
private def c561 : CNF.Clause Nat := [(91, false), (109, false)]
private def c562 : CNF.Clause Nat := [(92, false), (110, false)]
private def c563 : CNF.Clause Nat := [(90, false), (111, false)]
private def c564 : CNF.Clause Nat := [(91, false), (112, false)]
private def c565 : CNF.Clause Nat := [(92, false), (113, false)]
private def c566 : CNF.Clause Nat := [(93, false), (138, false)]
private def c567 : CNF.Clause Nat := [(94, false), (139, false)]
private def c568 : CNF.Clause Nat := [(95, false), (140, false)]
private def c569 : CNF.Clause Nat := [(93, false), (141, false)]
private def c570 : CNF.Clause Nat := [(94, false), (142, false)]
private def c571 : CNF.Clause Nat := [(95, false), (143, false)]
private def c572 : CNF.Clause Nat := [(96, false), (99, false)]
private def c573 : CNF.Clause Nat := [(97, false), (100, false)]
private def c574 : CNF.Clause Nat := [(98, false), (101, false)]
private def c575 : CNF.Clause Nat := [(102, false), (105, false)]
private def c576 : CNF.Clause Nat := [(103, false), (106, false)]
private def c577 : CNF.Clause Nat := [(104, false), (107, false)]
private def c578 : CNF.Clause Nat := [(108, false), (120, false)]
private def c579 : CNF.Clause Nat := [(109, false), (121, false)]
private def c580 : CNF.Clause Nat := [(110, false), (122, false)]
private def c581 : CNF.Clause Nat := [(111, false), (123, false)]
private def c582 : CNF.Clause Nat := [(112, false), (124, false)]
private def c583 : CNF.Clause Nat := [(113, false), (125, false)]
private def c584 : CNF.Clause Nat := [(114, false), (138, false)]
private def c585 : CNF.Clause Nat := [(115, false), (139, false)]
private def c586 : CNF.Clause Nat := [(116, false), (140, false)]
private def c587 : CNF.Clause Nat := [(114, false), (144, false)]
private def c588 : CNF.Clause Nat := [(115, false), (145, false)]
private def c589 : CNF.Clause Nat := [(116, false), (146, false)]
private def c590 : CNF.Clause Nat := [(117, false), (141, false)]
private def c591 : CNF.Clause Nat := [(118, false), (142, false)]
private def c592 : CNF.Clause Nat := [(119, false), (143, false)]
private def c593 : CNF.Clause Nat := [(117, false), (147, false)]
private def c594 : CNF.Clause Nat := [(118, false), (148, false)]
private def c595 : CNF.Clause Nat := [(119, false), (149, false)]
private def c596 : CNF.Clause Nat := [(120, false), (123, false)]
private def c597 : CNF.Clause Nat := [(121, false), (124, false)]
private def c598 : CNF.Clause Nat := [(122, false), (125, false)]
private def c599 : CNF.Clause Nat := [(126, false), (132, false)]
private def c600 : CNF.Clause Nat := [(127, false), (133, false)]
private def c601 : CNF.Clause Nat := [(128, false), (134, false)]
private def c602 : CNF.Clause Nat := [(129, false), (135, false)]
private def c603 : CNF.Clause Nat := [(130, false), (136, false)]
private def c604 : CNF.Clause Nat := [(131, false), (137, false)]
private def c605 : CNF.Clause Nat := [(132, false), (135, false)]
private def c606 : CNF.Clause Nat := [(133, false), (136, false)]
private def c607 : CNF.Clause Nat := [(134, false), (137, false)]
private def c608 : CNF.Clause Nat := [(138, false), (144, false)]
private def c609 : CNF.Clause Nat := [(139, false), (145, false)]
private def c610 : CNF.Clause Nat := [(140, false), (146, false)]
private def c611 : CNF.Clause Nat := [(141, false), (147, false)]
private def c612 : CNF.Clause Nat := [(142, false), (148, false)]
private def c613 : CNF.Clause Nat := [(143, false), (149, false)]
private def c614 : CNF.Clause Nat := [(144, false), (147, false)]
private def c615 : CNF.Clause Nat := [(145, false), (148, false)]
private def c616 : CNF.Clause Nat := [(146, false), (149, false)]
private def c617 : CNF.Clause Nat := [(150, false), (153, false)]
private def c618 : CNF.Clause Nat := [(151, false), (154, false)]
private def c619 : CNF.Clause Nat := [(152, false), (155, false)]
private def c620 : CNF.Clause Nat := [(150, false), (156, false)]
private def c621 : CNF.Clause Nat := [(151, false), (157, false)]
private def c622 : CNF.Clause Nat := [(152, false), (158, false)]
private def c623 : CNF.Clause Nat := [(150, false), (159, false)]
private def c624 : CNF.Clause Nat := [(151, false), (160, false)]
private def c625 : CNF.Clause Nat := [(152, false), (161, false)]
private def c626 : CNF.Clause Nat := [(150, false), (162, false)]
private def c627 : CNF.Clause Nat := [(151, false), (163, false)]
private def c628 : CNF.Clause Nat := [(152, false), (164, false)]
private def c629 : CNF.Clause Nat := [(153, false), (192, false)]
private def c630 : CNF.Clause Nat := [(154, false), (193, false)]
private def c631 : CNF.Clause Nat := [(155, false), (194, false)]
private def c632 : CNF.Clause Nat := [(156, false), (195, false)]
private def c633 : CNF.Clause Nat := [(157, false), (196, false)]
private def c634 : CNF.Clause Nat := [(158, false), (197, false)]
private def c635 : CNF.Clause Nat := [(159, false), (162, false)]
private def c636 : CNF.Clause Nat := [(160, false), (163, false)]
private def c637 : CNF.Clause Nat := [(161, false), (164, false)]
private def c638 : CNF.Clause Nat := [(159, false), (210, false)]
private def c639 : CNF.Clause Nat := [(160, false), (211, false)]
private def c640 : CNF.Clause Nat := [(161, false), (212, false)]
private def c641 : CNF.Clause Nat := [(159, false), (213, false)]
private def c642 : CNF.Clause Nat := [(160, false), (214, false)]
private def c643 : CNF.Clause Nat := [(161, false), (215, false)]
private def c644 : CNF.Clause Nat := [(162, false), (222, false)]
private def c645 : CNF.Clause Nat := [(163, false), (223, false)]
private def c646 : CNF.Clause Nat := [(164, false), (224, false)]
private def c647 : CNF.Clause Nat := [(162, false), (225, false)]
private def c648 : CNF.Clause Nat := [(163, false), (226, false)]
private def c649 : CNF.Clause Nat := [(164, false), (227, false)]
private def c650 : CNF.Clause Nat := [(165, false), (168, false)]
private def c651 : CNF.Clause Nat := [(166, false), (169, false)]
private def c652 : CNF.Clause Nat := [(167, false), (170, false)]
private def c653 : CNF.Clause Nat := [(165, false), (171, false)]
private def c654 : CNF.Clause Nat := [(166, false), (172, false)]
private def c655 : CNF.Clause Nat := [(167, false), (173, false)]
private def c656 : CNF.Clause Nat := [(165, false), (174, false)]
private def c657 : CNF.Clause Nat := [(166, false), (175, false)]
private def c658 : CNF.Clause Nat := [(167, false), (176, false)]
private def c659 : CNF.Clause Nat := [(165, false), (177, false)]
private def c660 : CNF.Clause Nat := [(166, false), (178, false)]
private def c661 : CNF.Clause Nat := [(167, false), (179, false)]
private def c662 : CNF.Clause Nat := [(168, false), (198, false)]
private def c663 : CNF.Clause Nat := [(169, false), (199, false)]
private def c664 : CNF.Clause Nat := [(170, false), (200, false)]
private def c665 : CNF.Clause Nat := [(171, false), (201, false)]
private def c666 : CNF.Clause Nat := [(172, false), (202, false)]
private def c667 : CNF.Clause Nat := [(173, false), (203, false)]
private def c668 : CNF.Clause Nat := [(174, false), (177, false)]
private def c669 : CNF.Clause Nat := [(175, false), (178, false)]
private def c670 : CNF.Clause Nat := [(176, false), (179, false)]
private def c671 : CNF.Clause Nat := [(174, false), (204, false)]
private def c672 : CNF.Clause Nat := [(175, false), (205, false)]
private def c673 : CNF.Clause Nat := [(176, false), (206, false)]
private def c674 : CNF.Clause Nat := [(174, false), (207, false)]
private def c675 : CNF.Clause Nat := [(175, false), (208, false)]
private def c676 : CNF.Clause Nat := [(176, false), (209, false)]
private def c677 : CNF.Clause Nat := [(177, false), (234, false)]
private def c678 : CNF.Clause Nat := [(178, false), (235, false)]
private def c679 : CNF.Clause Nat := [(179, false), (236, false)]
private def c680 : CNF.Clause Nat := [(177, false), (237, false)]
private def c681 : CNF.Clause Nat := [(178, false), (238, false)]
private def c682 : CNF.Clause Nat := [(179, false), (239, false)]
private def c683 : CNF.Clause Nat := [(180, false), (186, false)]
private def c684 : CNF.Clause Nat := [(181, false), (187, false)]
private def c685 : CNF.Clause Nat := [(182, false), (188, false)]
private def c686 : CNF.Clause Nat := [(183, false), (189, false)]
private def c687 : CNF.Clause Nat := [(184, false), (190, false)]
private def c688 : CNF.Clause Nat := [(185, false), (191, false)]
private def c689 : CNF.Clause Nat := [(186, false), (189, false)]
private def c690 : CNF.Clause Nat := [(187, false), (190, false)]
private def c691 : CNF.Clause Nat := [(188, false), (191, false)]
private def c692 : CNF.Clause Nat := [(192, false), (195, false)]
private def c693 : CNF.Clause Nat := [(193, false), (196, false)]
private def c694 : CNF.Clause Nat := [(194, false), (197, false)]
private def c695 : CNF.Clause Nat := [(198, false), (201, false)]
private def c696 : CNF.Clause Nat := [(199, false), (202, false)]
private def c697 : CNF.Clause Nat := [(200, false), (203, false)]
private def c698 : CNF.Clause Nat := [(204, false), (216, false)]
private def c699 : CNF.Clause Nat := [(205, false), (217, false)]
private def c700 : CNF.Clause Nat := [(206, false), (218, false)]
private def c701 : CNF.Clause Nat := [(207, false), (219, false)]
private def c702 : CNF.Clause Nat := [(208, false), (220, false)]
private def c703 : CNF.Clause Nat := [(209, false), (221, false)]
private def c704 : CNF.Clause Nat := [(210, false), (234, false)]
private def c705 : CNF.Clause Nat := [(211, false), (235, false)]
private def c706 : CNF.Clause Nat := [(212, false), (236, false)]
private def c707 : CNF.Clause Nat := [(210, false), (240, false)]
private def c708 : CNF.Clause Nat := [(211, false), (241, false)]
private def c709 : CNF.Clause Nat := [(212, false), (242, false)]
private def c710 : CNF.Clause Nat := [(213, false), (237, false)]
private def c711 : CNF.Clause Nat := [(214, false), (238, false)]
private def c712 : CNF.Clause Nat := [(215, false), (239, false)]
private def c713 : CNF.Clause Nat := [(213, false), (243, false)]
private def c714 : CNF.Clause Nat := [(214, false), (244, false)]
private def c715 : CNF.Clause Nat := [(215, false), (245, false)]
private def c716 : CNF.Clause Nat := [(216, false), (219, false)]
private def c717 : CNF.Clause Nat := [(217, false), (220, false)]
private def c718 : CNF.Clause Nat := [(218, false), (221, false)]
private def c719 : CNF.Clause Nat := [(222, false), (228, false)]
private def c720 : CNF.Clause Nat := [(223, false), (229, false)]
private def c721 : CNF.Clause Nat := [(224, false), (230, false)]
private def c722 : CNF.Clause Nat := [(225, false), (231, false)]
private def c723 : CNF.Clause Nat := [(226, false), (232, false)]
private def c724 : CNF.Clause Nat := [(227, false), (233, false)]
private def c725 : CNF.Clause Nat := [(228, false), (231, false)]
private def c726 : CNF.Clause Nat := [(229, false), (232, false)]
private def c727 : CNF.Clause Nat := [(230, false), (233, false)]
private def c728 : CNF.Clause Nat := [(234, false), (240, false)]
private def c729 : CNF.Clause Nat := [(235, false), (241, false)]
private def c730 : CNF.Clause Nat := [(236, false), (242, false)]
private def c731 : CNF.Clause Nat := [(237, false), (243, false)]
private def c732 : CNF.Clause Nat := [(238, false), (244, false)]
private def c733 : CNF.Clause Nat := [(239, false), (245, false)]
private def c734 : CNF.Clause Nat := [(240, false), (243, false)]
private def c735 : CNF.Clause Nat := [(241, false), (244, false)]
private def c736 : CNF.Clause Nat := [(242, false), (245, false)]
private def c737 : CNF.Clause Nat := [(0, true)]
private def c738 : CNF.Clause Nat := [(4, true)]
private def c739 : CNF.Clause Nat := [(20, true)]
private def c740 : CNF.Clause Nat := [(203, false), (172, true)]
private def c741 : CNF.Clause Nat := [(198, false), (169, true)]
private def c742 : CNF.Clause Nat := [(200, false), (169, true)]
private def c743 : CNF.Clause Nat := [(166, false)]
private def c744 : CNF.Clause Nat := [(187, false), (38, true)]
private def c745 : CNF.Clause Nat := [(186, false), (38, true)]
private def c746 : CNF.Clause Nat := [(189, false), (41, true)]
private def c747 : CNF.Clause Nat := [(23, false)]
private def c748 : CNF.Clause Nat := [(221, false), (46, true), (208, true)]
private def c749 : CNF.Clause Nat := [(216, false), (43, true), (205, true)]
private def c750 : CNF.Clause Nat := [(219, false), (46, true), (208, true)]
private def c751 : CNF.Clause Nat := [(22, false), (175, false)]
private def c752 : CNF.Clause Nat := [(80, false), (66, true), (75, true)]
private def c753 : CNF.Clause Nat := [(66, true), (75, true), (78, true)]
private def c754 : CNF.Clause Nat := [(101, false), (72, true)]
private def c755 : CNF.Clause Nat := [(97, false), (69, true)]
private def c756 : CNF.Clause Nat := [(100, false), (72, true)]
private def c757 : CNF.Clause Nat := [(66, false)]
private def c758 : CNF.Clause Nat := [(137, false), (33, true), (129, true)]
private def c759 : CNF.Clause Nat := [(133, false), (30, true), (126, true)]
private def c760 : CNF.Clause Nat := [(136, false), (33, true), (129, true)]
private def c761 : CNF.Clause Nat := [(78, false), (21, false)]
private def c762 : CNF.Clause Nat := [(94, false), (81, true), (90, true)]
private def c763 : CNF.Clause Nat := [(81, true), (90, true), (93, true)]
private def c764 : CNF.Clause Nat := [(107, false), (87, true)]
private def c765 : CNF.Clause Nat := [(103, false), (84, true)]
private def c766 : CNF.Clause Nat := [(106, false), (87, true)]
private def c767 : CNF.Clause Nat := [(81, false)]
private def c768 : CNF.Clause Nat := [(125, false), (27, true), (111, true)]
private def c769 : CNF.Clause Nat := [(121, false), (24, true), (108, true)]
private def c770 : CNF.Clause Nat := [(124, false), (27, true), (111, true)]
private def c771 : CNF.Clause Nat := [(90, false), (21, false)]
private def c772 : CNF.Clause Nat := [(149, false), (21, false)]
private def c773 : CNF.Clause Nat := [(145, false), (21, false)]
private def c774 : CNF.Clause Nat := [(148, false), (21, false)]
private def c775 : CNF.Clause Nat := [(21, false)]
private def c776 : CNF.Clause Nat := [(174, false), (178, true)]
private def c777 : CNF.Clause Nat := [(178, true)]
private def c778 : CNF.Clause Nat := [(197, false), (157, true)]
private def c779 : CNF.Clause Nat := [(192, false), (154, true)]
private def c780 : CNF.Clause Nat := [(194, false), (154, true)]
private def c781 : CNF.Clause Nat := [(151, false)]
private def c782 : CNF.Clause Nat := [(233, false), (226, true)]
private def c783 : CNF.Clause Nat := [(228, false), (223, true)]
private def c784 : CNF.Clause Nat := [(230, false), (223, true)]
private def c785 : CNF.Clause Nat := [(163, false)]
private def c786 : CNF.Clause Nat := [(164, false), (160, true)]
private def c787 : CNF.Clause Nat := [(160, true)]
private def c788 : CNF.Clause Nat := [(245, false)]
private def c789 : CNF.Clause Nat := [(243, false)]
private def c790 : CNF.Clause Nat := [(240, false)]
private def c791 : CNF.Clause Nat := []
private def mini740 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(3, false), (7, false)], [(1, true), (2, true), (3, true)], [(6, false), (7, false)], [(4, true), (5, true), (6, true)], [(1, false), (4, false)]]⟩
refute_hints unsat740 mini740 9
theorem step740 (a : Nat → Bool) (h738 : c738.eval a = true) (h360 : c360.eval a = true) (h505 : c505.eval a = true) (h85 : c85.eval a = true) (h667 : c667.eval a = true) (h229 : c229.eval a = true) (h500 : c500.eval a = true) : c740.eval a = true := by
  cases hc : c740.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 63, 64, 65, 171, 172, 173, 203] : Array Nat)[k]!)
    have u0 := negUnit (i := 203) (p := false) hc (by decide)
    have u1 := negUnit (i := 172) (p := true) hc (by decide)
    apply clash mini740 unsat740 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h360, (Bool.and_eq_true_iff.mpr ⟨h505, (Bool.and_eq_true_iff.mpr ⟨h85, (Bool.and_eq_true_iff.mpr ⟨h667, (Bool.and_eq_true_iff.mpr ⟨h229, (Bool.and_eq_true_iff.mpr ⟨h500, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini741 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(1, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, false), (7, false)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat741 mini741 9
theorem step741 (a : Nat → Bool) (h738 : c738.eval a = true) (h357 : c357.eval a = true) (h497 : c497.eval a = true) (h81 : c81.eval a = true) (h662 : c662.eval a = true) (h225 : c225.eval a = true) (h496 : c496.eval a = true) : c741.eval a = true := by
  cases hc : c741.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 60, 61, 62, 168, 169, 170, 198] : Array Nat)[k]!)
    have u0 := negUnit (i := 198) (p := false) hc (by decide)
    have u1 := negUnit (i := 169) (p := true) hc (by decide)
    apply clash mini741 unsat741 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h357, (Bool.and_eq_true_iff.mpr ⟨h497, (Bool.and_eq_true_iff.mpr ⟨h81, (Bool.and_eq_true_iff.mpr ⟨h662, (Bool.and_eq_true_iff.mpr ⟨h225, (Bool.and_eq_true_iff.mpr ⟨h496, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini742 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(3, false), (7, false)], [(6, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(1, false), (4, false)]]⟩
refute_hints unsat742 mini742 9
theorem step742 (a : Nat → Bool) (h738 : c738.eval a = true) (h357 : c357.eval a = true) (h499 : c499.eval a = true) (h664 : c664.eval a = true) (h81 : c81.eval a = true) (h225 : c225.eval a = true) (h494 : c494.eval a = true) : c742.eval a = true := by
  cases hc : c742.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 60, 61, 62, 168, 169, 170, 200] : Array Nat)[k]!)
    have u0 := negUnit (i := 200) (p := false) hc (by decide)
    have u1 := negUnit (i := 169) (p := true) hc (by decide)
    apply clash mini742 unsat742 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h357, (Bool.and_eq_true_iff.mpr ⟨h499, (Bool.and_eq_true_iff.mpr ⟨h664, (Bool.and_eq_true_iff.mpr ⟨h81, (Bool.and_eq_true_iff.mpr ⟨h225, (Bool.and_eq_true_iff.mpr ⟨h494, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini743 : CNF Nat := ⟨#[[(4, true)], [(0, true)], [(0, false), (2, false)], [(4, false), (5, false)], [(4, false), (7, false)], [(11, false), (5, true)], [(9, false), (5, true)], [(14, false), (7, true)], [(9, true), (10, true), (11, true)], [(10, false), (13, false)], [(12, true), (13, true), (14, true)], [(1, false), (12, false)], [(6, false), (12, false)], [(1, true), (2, true), (3, true)], [(6, true), (7, true), (8, true)], [(3, false), (8, false)]]⟩
refute_hints unsat743 mini743 16
theorem step743 (a : Nat → Bool) (h738 : c738.eval a = true) (h360 : c360.eval a = true) (h651 : c651.eval a = true) (h654 : c654.eval a = true) (h742 : c742.eval a = true) (h741 : c741.eval a = true) (h740 : c740.eval a = true) (h265 : c265.eval a = true) (h696 : c696.eval a = true) (h269 : c269.eval a = true) (h503 : c503.eval a = true) (h665 : c665.eval a = true) (h85 : c85.eval a = true) (h229 : c229.eval a = true) (h502 : c502.eval a = true) : c743.eval a = true := by
  cases hc : c743.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 63, 64, 65, 166, 169, 171, 172, 173, 198, 199, 200, 201, 202, 203] : Array Nat)[k]!)
    have u0 := negUnit (i := 166) (p := false) hc (by decide)
    apply clash mini743 unsat743 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h360, (Bool.and_eq_true_iff.mpr ⟨h651, (Bool.and_eq_true_iff.mpr ⟨h654, (Bool.and_eq_true_iff.mpr ⟨h742, (Bool.and_eq_true_iff.mpr ⟨h741, (Bool.and_eq_true_iff.mpr ⟨h740, (Bool.and_eq_true_iff.mpr ⟨h265, (Bool.and_eq_true_iff.mpr ⟨h696, (Bool.and_eq_true_iff.mpr ⟨h269, (Bool.and_eq_true_iff.mpr ⟨h503, (Bool.and_eq_true_iff.mpr ⟨h665, (Bool.and_eq_true_iff.mpr ⟨h85, (Bool.and_eq_true_iff.mpr ⟨h229, (Bool.and_eq_true_iff.mpr ⟨h502, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini744 : CNF Nat := ⟨#[[(7, true)], [(3, false)], [(0, true)], [(0, false), (6, false)], [(2, false), (7, false)], [(1, true), (2, true), (3, true)], [(5, false), (7, false)], [(4, true), (5, true), (6, true)], [(1, false), (4, false)]]⟩
refute_hints unsat744 mini744 9
theorem step744 (a : Nat → Bool) (h739 : c739.eval a = true) (h388 : c388.eval a = true) (h450 : c450.eval a = true) (h49 : c49.eval a = true) (h684 : c684.eval a = true) (h241 : c241.eval a = true) (h446 : c446.eval a = true) : c744.eval a = true := by
  cases hc : c744.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[20, 36, 37, 38, 180, 181, 182, 187] : Array Nat)[k]!)
    have u0 := negUnit (i := 187) (p := false) hc (by decide)
    have u1 := negUnit (i := 38) (p := true) hc (by decide)
    apply clash mini744 unsat744 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h739, (Bool.and_eq_true_iff.mpr ⟨h388, (Bool.and_eq_true_iff.mpr ⟨h450, (Bool.and_eq_true_iff.mpr ⟨h49, (Bool.and_eq_true_iff.mpr ⟨h684, (Bool.and_eq_true_iff.mpr ⟨h241, (Bool.and_eq_true_iff.mpr ⟨h446, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini745 : CNF Nat := ⟨#[[(7, true)], [(3, false)], [(0, true)], [(0, false), (6, false)], [(1, false), (7, false)], [(4, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(2, false), (5, false)]]⟩
refute_hints unsat745 mini745 9
theorem step745 (a : Nat → Bool) (h739 : c739.eval a = true) (h388 : c388.eval a = true) (h449 : c449.eval a = true) (h683 : c683.eval a = true) (h49 : c49.eval a = true) (h241 : c241.eval a = true) (h447 : c447.eval a = true) : c745.eval a = true := by
  cases hc : c745.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[20, 36, 37, 38, 180, 181, 182, 186] : Array Nat)[k]!)
    have u0 := negUnit (i := 186) (p := false) hc (by decide)
    have u1 := negUnit (i := 38) (p := true) hc (by decide)
    apply clash mini745 unsat745 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h739, (Bool.and_eq_true_iff.mpr ⟨h388, (Bool.and_eq_true_iff.mpr ⟨h449, (Bool.and_eq_true_iff.mpr ⟨h683, (Bool.and_eq_true_iff.mpr ⟨h49, (Bool.and_eq_true_iff.mpr ⟨h241, (Bool.and_eq_true_iff.mpr ⟨h447, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini746 : CNF Nat := ⟨#[[(7, true)], [(3, false)], [(0, true)], [(0, false), (6, false)], [(1, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, false), (7, false)], [(4, true), (5, true), (6, true)], [(2, false), (5, false)]]⟩
refute_hints unsat746 mini746 9
theorem step746 (a : Nat → Bool) (h739 : c739.eval a = true) (h391 : c391.eval a = true) (h455 : c455.eval a = true) (h53 : c53.eval a = true) (h686 : c686.eval a = true) (h245 : c245.eval a = true) (h453 : c453.eval a = true) : c746.eval a = true := by
  cases hc : c746.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[20, 39, 40, 41, 183, 184, 185, 189] : Array Nat)[k]!)
    have u0 := negUnit (i := 189) (p := false) hc (by decide)
    have u1 := negUnit (i := 41) (p := true) hc (by decide)
    apply clash mini746 unsat746 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h739, (Bool.and_eq_true_iff.mpr ⟨h391, (Bool.and_eq_true_iff.mpr ⟨h455, (Bool.and_eq_true_iff.mpr ⟨h53, (Bool.and_eq_true_iff.mpr ⟨h686, (Bool.and_eq_true_iff.mpr ⟨h245, (Bool.and_eq_true_iff.mpr ⟨h453, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini747 : CNF Nat := ⟨#[[(1, true)], [(0, true)], [(0, false), (8, false)], [(1, false), (2, false)], [(1, false), (5, false)], [(10, false), (2, true)], [(9, false), (2, true)], [(12, false), (5, true)], [(9, true), (10, true), (11, true)], [(11, false), (14, false)], [(12, true), (13, true), (14, true)], [(4, false), (13, false)], [(7, false), (13, false)], [(3, true), (4, true), (5, true)], [(6, true), (7, true), (8, true)], [(3, false), (6, false)]]⟩
refute_hints unsat747 mini747 16
theorem step747 (a : Nat → Bool) (h739 : c739.eval a = true) (h391 : c391.eval a = true) (h406 : c406.eval a = true) (h409 : c409.eval a = true) (h744 : c744.eval a = true) (h745 : c745.eval a = true) (h746 : c746.eval a = true) (h249 : c249.eval a = true) (h691 : c691.eval a = true) (h253 : c253.eval a = true) (h456 : c456.eval a = true) (h687 : c687.eval a = true) (h53 : c53.eval a = true) (h245 : c245.eval a = true) (h452 : c452.eval a = true) : c747.eval a = true := by
  cases hc : c747.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[20, 23, 38, 39, 40, 41, 183, 184, 185, 186, 187, 188, 189, 190, 191] : Array Nat)[k]!)
    have u0 := negUnit (i := 23) (p := false) hc (by decide)
    apply clash mini747 unsat747 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h739, (Bool.and_eq_true_iff.mpr ⟨h391, (Bool.and_eq_true_iff.mpr ⟨h406, (Bool.and_eq_true_iff.mpr ⟨h409, (Bool.and_eq_true_iff.mpr ⟨h744, (Bool.and_eq_true_iff.mpr ⟨h745, (Bool.and_eq_true_iff.mpr ⟨h746, (Bool.and_eq_true_iff.mpr ⟨h249, (Bool.and_eq_true_iff.mpr ⟨h691, (Bool.and_eq_true_iff.mpr ⟨h253, (Bool.and_eq_true_iff.mpr ⟨h456, (Bool.and_eq_true_iff.mpr ⟨h687, (Bool.and_eq_true_iff.mpr ⟨h53, (Bool.and_eq_true_iff.mpr ⟨h245, (Bool.and_eq_true_iff.mpr ⟨h452, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini748 : CNF Nat := ⟨#[[(6, true)], [(1, false)], [(4, false)], [(2, false), (6, false)], [(0, true), (1, true), (2, true)], [(5, false), (6, false)], [(3, true), (4, true), (5, true)], [(0, false), (3, false)]]⟩
refute_hints unsat748 mini748 8
theorem step748 (a : Nat → Bool) (h469 : c469.eval a = true) (h61 : c61.eval a = true) (h703 : c703.eval a = true) (h277 : c277.eval a = true) (h464 : c464.eval a = true) : c748.eval a = true := by
  cases hc : c748.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[45, 46, 47, 207, 208, 209, 221] : Array Nat)[k]!)
    have u0 := negUnit (i := 221) (p := false) hc (by decide)
    have u1 := negUnit (i := 46) (p := true) hc (by decide)
    have u2 := negUnit (i := 208) (p := true) hc (by decide)
    apply clash mini748 unsat748 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h469, (Bool.and_eq_true_iff.mpr ⟨h61, (Bool.and_eq_true_iff.mpr ⟨h703, (Bool.and_eq_true_iff.mpr ⟨h277, (Bool.and_eq_true_iff.mpr ⟨h464, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini749 : CNF Nat := ⟨#[[(6, true)], [(1, false)], [(4, false)], [(0, false), (6, false)], [(0, true), (1, true), (2, true)], [(3, false), (6, false)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat749 mini749 8
theorem step749 (a : Nat → Bool) (h461 : c461.eval a = true) (h57 : c57.eval a = true) (h698 : c698.eval a = true) (h273 : c273.eval a = true) (h460 : c460.eval a = true) : c749.eval a = true := by
  cases hc : c749.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[42, 43, 44, 204, 205, 206, 216] : Array Nat)[k]!)
    have u0 := negUnit (i := 216) (p := false) hc (by decide)
    have u1 := negUnit (i := 43) (p := true) hc (by decide)
    have u2 := negUnit (i := 205) (p := true) hc (by decide)
    apply clash mini749 unsat749 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h461, (Bool.and_eq_true_iff.mpr ⟨h57, (Bool.and_eq_true_iff.mpr ⟨h698, (Bool.and_eq_true_iff.mpr ⟨h273, (Bool.and_eq_true_iff.mpr ⟨h460, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini750 : CNF Nat := ⟨#[[(6, true)], [(1, false)], [(4, false)], [(0, false), (6, false)], [(3, false), (6, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat750 mini750 8
theorem step750 (a : Nat → Bool) (h467 : c467.eval a = true) (h701 : c701.eval a = true) (h61 : c61.eval a = true) (h277 : c277.eval a = true) (h466 : c466.eval a = true) : c750.eval a = true := by
  cases hc : c750.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[45, 46, 47, 207, 208, 209, 219] : Array Nat)[k]!)
    have u0 := negUnit (i := 219) (p := false) hc (by decide)
    have u1 := negUnit (i := 46) (p := true) hc (by decide)
    have u2 := negUnit (i := 208) (p := true) hc (by decide)
    apply clash mini750 unsat750 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h467, (Bool.and_eq_true_iff.mpr ⟨h701, (Bool.and_eq_true_iff.mpr ⟨h61, (Bool.and_eq_true_iff.mpr ⟨h277, (Bool.and_eq_true_iff.mpr ⟨h466, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini751 : CNF Nat := ⟨#[[(0, true)], [(5, true)], [(5, false), (7, false)], [(5, false), (9, false)], [(0, false), (2, false)], [(0, false), (4, false)], [(10, false), (2, true), (7, true)], [(15, false), (4, true), (9, true)], [(13, false), (4, true), (9, true)], [(13, true), (14, true), (15, true)], [(11, false), (14, false)], [(10, true), (11, true), (12, true)], [(3, false), (12, false)], [(8, false), (12, false)], [(1, true), (2, true), (3, true)], [(6, true), (7, true), (8, true)], [(1, false), (6, false)]]⟩
refute_hints unsat751 mini751 17
theorem step751 (a : Nat → Bool) (h672 : c672.eval a = true) (h675 : c675.eval a = true) (h411 : c411.eval a = true) (h414 : c414.eval a = true) (h749 : c749.eval a = true) (h748 : c748.eval a = true) (h750 : c750.eval a = true) (h293 : c293.eval a = true) (h717 : c717.eval a = true) (h289 : c289.eval a = true) (h463 : c463.eval a = true) (h700 : c700.eval a = true) (h57 : c57.eval a = true) (h273 : c273.eval a = true) (h458 : c458.eval a = true) : c751.eval a = true := by
  cases hc : c751.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[22, 42, 43, 44, 46, 175, 204, 205, 206, 208, 216, 217, 218, 219, 220, 221] : Array Nat)[k]!)
    have u0 := negUnit (i := 22) (p := false) hc (by decide)
    have u1 := negUnit (i := 175) (p := false) hc (by decide)
    apply clash mini751 unsat751 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h672, (Bool.and_eq_true_iff.mpr ⟨h675, (Bool.and_eq_true_iff.mpr ⟨h411, (Bool.and_eq_true_iff.mpr ⟨h414, (Bool.and_eq_true_iff.mpr ⟨h749, (Bool.and_eq_true_iff.mpr ⟨h748, (Bool.and_eq_true_iff.mpr ⟨h750, (Bool.and_eq_true_iff.mpr ⟨h293, (Bool.and_eq_true_iff.mpr ⟨h717, (Bool.and_eq_true_iff.mpr ⟨h289, (Bool.and_eq_true_iff.mpr ⟨h463, (Bool.and_eq_true_iff.mpr ⟨h700, (Bool.and_eq_true_iff.mpr ⟨h57, (Bool.and_eq_true_iff.mpr ⟨h273, (Bool.and_eq_true_iff.mpr ⟨h458, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini752 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(2, false), (6, false)], [(0, true), (1, true), (2, true)], [(5, false), (6, false)], [(3, true), (4, true), (5, true)], [(1, false), (4, false)]]⟩
refute_hints unsat752 mini752 8
theorem step752 (a : Nat → Bool) (h517 : c517.eval a = true) (h89 : c89.eval a = true) (h526 : c526.eval a = true) (h101 : c101.eval a = true) (h513 : c513.eval a = true) : c752.eval a = true := by
  cases hc : c752.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[66, 67, 68, 75, 76, 77, 80] : Array Nat)[k]!)
    have u0 := negUnit (i := 80) (p := false) hc (by decide)
    have u1 := negUnit (i := 66) (p := true) hc (by decide)
    have u2 := negUnit (i := 75) (p := true) hc (by decide)
    apply clash mini752 unsat752 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h517, (Bool.and_eq_true_iff.mpr ⟨h89, (Bool.and_eq_true_iff.mpr ⟨h526, (Bool.and_eq_true_iff.mpr ⟨h101, (Bool.and_eq_true_iff.mpr ⟨h513, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini753 : CNF Nat := ⟨#[[(0, false)], [(3, false)], [(6, false)], [(8, false), (0, true), (3, true)], [(6, true), (7, true), (8, true)], [(1, false), (7, false)], [(4, false), (7, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat753 mini753 10
theorem step753 (a : Nat → Bool) (h752 : c752.eval a = true) (h105 : c105.eval a = true) (h516 : c516.eval a = true) (h525 : c525.eval a = true) (h89 : c89.eval a = true) (h101 : c101.eval a = true) (h514 : c514.eval a = true) : c753.eval a = true := by
  cases hc : c753.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[66, 67, 68, 75, 76, 77, 78, 79, 80] : Array Nat)[k]!)
    have u0 := negUnit (i := 66) (p := true) hc (by decide)
    have u1 := negUnit (i := 75) (p := true) hc (by decide)
    have u2 := negUnit (i := 78) (p := true) hc (by decide)
    apply clash mini753 unsat753 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h752, (Bool.and_eq_true_iff.mpr ⟨h105, (Bool.and_eq_true_iff.mpr ⟨h516, (Bool.and_eq_true_iff.mpr ⟨h525, (Bool.and_eq_true_iff.mpr ⟨h89, (Bool.and_eq_true_iff.mpr ⟨h101, (Bool.and_eq_true_iff.mpr ⟨h514, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini754 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(3, false), (7, false)], [(1, true), (2, true), (3, true)], [(6, false), (7, false)], [(4, true), (5, true), (6, true)], [(2, false), (5, false)]]⟩
refute_hints unsat754 mini754 9
theorem step754 (a : Nat → Bool) (h737 : c737.eval a = true) (h335 : c335.eval a = true) (h373 : c373.eval a = true) (h13 : c13.eval a = true) (h523 : c523.eval a = true) (h97 : c97.eval a = true) (h369 : c369.eval a = true) : c754.eval a = true := by
  cases hc : c754.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 9, 10, 11, 72, 73, 74, 101] : Array Nat)[k]!)
    have u0 := negUnit (i := 101) (p := false) hc (by decide)
    have u1 := negUnit (i := 72) (p := true) hc (by decide)
    apply clash mini754 unsat754 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h335, (Bool.and_eq_true_iff.mpr ⟨h373, (Bool.and_eq_true_iff.mpr ⟨h13, (Bool.and_eq_true_iff.mpr ⟨h523, (Bool.and_eq_true_iff.mpr ⟨h97, (Bool.and_eq_true_iff.mpr ⟨h369, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini755 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(2, false), (7, false)], [(1, true), (2, true), (3, true)], [(5, false), (7, false)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat755 mini755 9
theorem step755 (a : Nat → Bool) (h737 : c737.eval a = true) (h332 : c332.eval a = true) (h366 : c366.eval a = true) (h9 : c9.eval a = true) (h519 : c519.eval a = true) (h93 : c93.eval a = true) (h364 : c364.eval a = true) : c755.eval a = true := by
  cases hc : c755.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 6, 7, 8, 69, 70, 71, 97] : Array Nat)[k]!)
    have u0 := negUnit (i := 97) (p := false) hc (by decide)
    have u1 := negUnit (i := 69) (p := true) hc (by decide)
    apply clash mini755 unsat755 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h332, (Bool.and_eq_true_iff.mpr ⟨h366, (Bool.and_eq_true_iff.mpr ⟨h9, (Bool.and_eq_true_iff.mpr ⟨h519, (Bool.and_eq_true_iff.mpr ⟨h93, (Bool.and_eq_true_iff.mpr ⟨h364, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini756 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(2, false), (7, false)], [(5, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat756 mini756 9
theorem step756 (a : Nat → Bool) (h737 : c737.eval a = true) (h335 : c335.eval a = true) (h372 : c372.eval a = true) (h522 : c522.eval a = true) (h13 : c13.eval a = true) (h97 : c97.eval a = true) (h370 : c370.eval a = true) : c756.eval a = true := by
  cases hc : c756.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 9, 10, 11, 72, 73, 74, 100] : Array Nat)[k]!)
    have u0 := negUnit (i := 100) (p := false) hc (by decide)
    have u1 := negUnit (i := 72) (p := true) hc (by decide)
    apply clash mini756 unsat756 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h335, (Bool.and_eq_true_iff.mpr ⟨h372, (Bool.and_eq_true_iff.mpr ⟨h522, (Bool.and_eq_true_iff.mpr ⟨h13, (Bool.and_eq_true_iff.mpr ⟨h97, (Bool.and_eq_true_iff.mpr ⟨h370, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini757 : CNF Nat := ⟨#[[(4, true)], [(0, true)], [(0, false), (1, false)], [(4, false), (5, false)], [(4, false), (8, false)], [(10, false), (5, true)], [(13, false), (8, true)], [(14, false), (8, true)], [(12, true), (13, true), (14, true)], [(9, false), (12, false)], [(9, true), (10, true), (11, true)], [(3, false), (11, false)], [(7, false), (11, false)], [(1, true), (2, true), (3, true)], [(5, true), (6, true), (7, true)], [(2, false), (6, false)]]⟩
refute_hints unsat757 mini757 16
theorem step757 (a : Nat → Bool) (h737 : c737.eval a = true) (h332 : c332.eval a = true) (h506 : c506.eval a = true) (h509 : c509.eval a = true) (h755 : c755.eval a = true) (h756 : c756.eval a = true) (h754 : c754.eval a = true) (h133 : c133.eval a = true) (h572 : c572.eval a = true) (h129 : c129.eval a = true) (h367 : c367.eval a = true) (h520 : c520.eval a = true) (h9 : c9.eval a = true) (h93 : c93.eval a = true) (h363 : c363.eval a = true) : c757.eval a = true := by
  cases hc : c757.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 6, 7, 8, 66, 69, 70, 71, 72, 96, 97, 98, 99, 100, 101] : Array Nat)[k]!)
    have u0 := negUnit (i := 66) (p := false) hc (by decide)
    apply clash mini757 unsat757 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h332, (Bool.and_eq_true_iff.mpr ⟨h506, (Bool.and_eq_true_iff.mpr ⟨h509, (Bool.and_eq_true_iff.mpr ⟨h755, (Bool.and_eq_true_iff.mpr ⟨h756, (Bool.and_eq_true_iff.mpr ⟨h754, (Bool.and_eq_true_iff.mpr ⟨h133, (Bool.and_eq_true_iff.mpr ⟨h572, (Bool.and_eq_true_iff.mpr ⟨h129, (Bool.and_eq_true_iff.mpr ⟨h367, (Bool.and_eq_true_iff.mpr ⟨h520, (Bool.and_eq_true_iff.mpr ⟨h9, (Bool.and_eq_true_iff.mpr ⟨h93, (Bool.and_eq_true_iff.mpr ⟨h363, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini758 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(2, false), (6, false)], [(0, true), (1, true), (2, true)], [(5, false), (6, false)], [(3, true), (4, true), (5, true)], [(1, false), (4, false)]]⟩
refute_hints unsat758 mini758 8
theorem step758 (a : Nat → Bool) (h445 : c445.eval a = true) (h45 : c45.eval a = true) (h604 : c604.eval a = true) (h173 : c173.eval a = true) (h441 : c441.eval a = true) : c758.eval a = true := by
  cases hc : c758.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[33, 34, 35, 129, 130, 131, 137] : Array Nat)[k]!)
    have u0 := negUnit (i := 137) (p := false) hc (by decide)
    have u1 := negUnit (i := 33) (p := true) hc (by decide)
    have u2 := negUnit (i := 129) (p := true) hc (by decide)
    apply clash mini758 unsat758 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h445, (Bool.and_eq_true_iff.mpr ⟨h45, (Bool.and_eq_true_iff.mpr ⟨h604, (Bool.and_eq_true_iff.mpr ⟨h173, (Bool.and_eq_true_iff.mpr ⟨h441, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini759 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(1, false), (6, false)], [(0, true), (1, true), (2, true)], [(4, false), (6, false)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat759 mini759 8
theorem step759 (a : Nat → Bool) (h438 : c438.eval a = true) (h41 : c41.eval a = true) (h600 : c600.eval a = true) (h169 : c169.eval a = true) (h436 : c436.eval a = true) : c759.eval a = true := by
  cases hc : c759.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[30, 31, 32, 126, 127, 128, 133] : Array Nat)[k]!)
    have u0 := negUnit (i := 133) (p := false) hc (by decide)
    have u1 := negUnit (i := 30) (p := true) hc (by decide)
    have u2 := negUnit (i := 126) (p := true) hc (by decide)
    apply clash mini759 unsat759 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h438, (Bool.and_eq_true_iff.mpr ⟨h41, (Bool.and_eq_true_iff.mpr ⟨h600, (Bool.and_eq_true_iff.mpr ⟨h169, (Bool.and_eq_true_iff.mpr ⟨h436, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini760 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(1, false), (6, false)], [(4, false), (6, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat760 mini760 8
theorem step760 (a : Nat → Bool) (h444 : c444.eval a = true) (h603 : c603.eval a = true) (h45 : c45.eval a = true) (h173 : c173.eval a = true) (h442 : c442.eval a = true) : c760.eval a = true := by
  cases hc : c760.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[33, 34, 35, 129, 130, 131, 136] : Array Nat)[k]!)
    have u0 := negUnit (i := 136) (p := false) hc (by decide)
    have u1 := negUnit (i := 33) (p := true) hc (by decide)
    have u2 := negUnit (i := 129) (p := true) hc (by decide)
    apply clash mini760 unsat760 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h444, (Bool.and_eq_true_iff.mpr ⟨h603, (Bool.and_eq_true_iff.mpr ⟨h45, (Bool.and_eq_true_iff.mpr ⟨h173, (Bool.and_eq_true_iff.mpr ⟨h442, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini761 : CNF Nat := ⟨#[[(5, true)], [(0, true)], [(5, false), (6, false)], [(5, false), (9, false)], [(0, false), (1, false)], [(0, false), (4, false)], [(11, false), (1, true), (6, true)], [(15, false), (4, true), (9, true)], [(14, false), (4, true), (9, true)], [(13, true), (14, true), (15, true)], [(10, false), (13, false)], [(10, true), (11, true), (12, true)], [(3, false), (12, false)], [(8, false), (12, false)], [(1, true), (2, true), (3, true)], [(6, true), (7, true), (8, true)], [(2, false), (7, false)]]⟩
refute_hints unsat761 mini761 17
theorem step761 (a : Nat → Bool) (h533 : c533.eval a = true) (h536 : c536.eval a = true) (h398 : c398.eval a = true) (h401 : c401.eval a = true) (h759 : c759.eval a = true) (h758 : c758.eval a = true) (h760 : c760.eval a = true) (h181 : c181.eval a = true) (h605 : c605.eval a = true) (h177 : c177.eval a = true) (h439 : c439.eval a = true) (h601 : c601.eval a = true) (h41 : c41.eval a = true) (h169 : c169.eval a = true) (h435 : c435.eval a = true) : c761.eval a = true := by
  cases hc : c761.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 30, 31, 32, 33, 78, 126, 127, 128, 129, 132, 133, 134, 135, 136, 137] : Array Nat)[k]!)
    have u0 := negUnit (i := 78) (p := false) hc (by decide)
    have u1 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini761 unsat761 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h533, (Bool.and_eq_true_iff.mpr ⟨h536, (Bool.and_eq_true_iff.mpr ⟨h398, (Bool.and_eq_true_iff.mpr ⟨h401, (Bool.and_eq_true_iff.mpr ⟨h759, (Bool.and_eq_true_iff.mpr ⟨h758, (Bool.and_eq_true_iff.mpr ⟨h760, (Bool.and_eq_true_iff.mpr ⟨h181, (Bool.and_eq_true_iff.mpr ⟨h605, (Bool.and_eq_true_iff.mpr ⟨h177, (Bool.and_eq_true_iff.mpr ⟨h439, (Bool.and_eq_true_iff.mpr ⟨h601, (Bool.and_eq_true_iff.mpr ⟨h41, (Bool.and_eq_true_iff.mpr ⟨h169, (Bool.and_eq_true_iff.mpr ⟨h435, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini762 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(1, false), (6, false)], [(0, true), (1, true), (2, true)], [(4, false), (6, false)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat762 mini762 8
theorem step762 (a : Nat → Bool) (h549 : c549.eval a = true) (h109 : c109.eval a = true) (h558 : c558.eval a = true) (h121 : c121.eval a = true) (h547 : c547.eval a = true) : c762.eval a = true := by
  cases hc : c762.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[81, 82, 83, 90, 91, 92, 94] : Array Nat)[k]!)
    have u0 := negUnit (i := 94) (p := false) hc (by decide)
    have u1 := negUnit (i := 81) (p := true) hc (by decide)
    have u2 := negUnit (i := 90) (p := true) hc (by decide)
    apply clash mini762 unsat762 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h549, (Bool.and_eq_true_iff.mpr ⟨h109, (Bool.and_eq_true_iff.mpr ⟨h558, (Bool.and_eq_true_iff.mpr ⟨h121, (Bool.and_eq_true_iff.mpr ⟨h547, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini763 : CNF Nat := ⟨#[[(0, false)], [(3, false)], [(6, false)], [(7, false), (0, true), (3, true)], [(6, true), (7, true), (8, true)], [(2, false), (8, false)], [(5, false), (8, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(1, false), (4, false)]]⟩
refute_hints unsat763 mini763 10
theorem step763 (a : Nat → Bool) (h762 : c762.eval a = true) (h125 : c125.eval a = true) (h550 : c550.eval a = true) (h559 : c559.eval a = true) (h109 : c109.eval a = true) (h121 : c121.eval a = true) (h546 : c546.eval a = true) : c763.eval a = true := by
  cases hc : c763.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[81, 82, 83, 90, 91, 92, 93, 94, 95] : Array Nat)[k]!)
    have u0 := negUnit (i := 81) (p := true) hc (by decide)
    have u1 := negUnit (i := 90) (p := true) hc (by decide)
    have u2 := negUnit (i := 93) (p := true) hc (by decide)
    apply clash mini763 unsat763 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h762, (Bool.and_eq_true_iff.mpr ⟨h125, (Bool.and_eq_true_iff.mpr ⟨h550, (Bool.and_eq_true_iff.mpr ⟨h559, (Bool.and_eq_true_iff.mpr ⟨h109, (Bool.and_eq_true_iff.mpr ⟨h121, (Bool.and_eq_true_iff.mpr ⟨h546, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini764 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(3, false), (7, false)], [(1, true), (2, true), (3, true)], [(6, false), (7, false)], [(4, true), (5, true), (6, true)], [(2, false), (5, false)]]⟩
refute_hints unsat764 mini764 9
theorem step764 (a : Nat → Bool) (h737 : c737.eval a = true) (h341 : c341.eval a = true) (h385 : c385.eval a = true) (h21 : c21.eval a = true) (h556 : c556.eval a = true) (h117 : c117.eval a = true) (h381 : c381.eval a = true) : c764.eval a = true := by
  cases hc : c764.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 15, 16, 17, 87, 88, 89, 107] : Array Nat)[k]!)
    have u0 := negUnit (i := 107) (p := false) hc (by decide)
    have u1 := negUnit (i := 87) (p := true) hc (by decide)
    apply clash mini764 unsat764 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h341, (Bool.and_eq_true_iff.mpr ⟨h385, (Bool.and_eq_true_iff.mpr ⟨h21, (Bool.and_eq_true_iff.mpr ⟨h556, (Bool.and_eq_true_iff.mpr ⟨h117, (Bool.and_eq_true_iff.mpr ⟨h381, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini765 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(2, false), (7, false)], [(1, true), (2, true), (3, true)], [(5, false), (7, false)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat765 mini765 9
theorem step765 (a : Nat → Bool) (h737 : c737.eval a = true) (h338 : c338.eval a = true) (h378 : c378.eval a = true) (h17 : c17.eval a = true) (h552 : c552.eval a = true) (h113 : c113.eval a = true) (h376 : c376.eval a = true) : c765.eval a = true := by
  cases hc : c765.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 12, 13, 14, 84, 85, 86, 103] : Array Nat)[k]!)
    have u0 := negUnit (i := 103) (p := false) hc (by decide)
    have u1 := negUnit (i := 84) (p := true) hc (by decide)
    apply clash mini765 unsat765 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h338, (Bool.and_eq_true_iff.mpr ⟨h378, (Bool.and_eq_true_iff.mpr ⟨h17, (Bool.and_eq_true_iff.mpr ⟨h552, (Bool.and_eq_true_iff.mpr ⟨h113, (Bool.and_eq_true_iff.mpr ⟨h376, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini766 : CNF Nat := ⟨#[[(7, true)], [(4, false)], [(0, true)], [(0, false), (1, false)], [(2, false), (7, false)], [(5, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat766 mini766 9
theorem step766 (a : Nat → Bool) (h737 : c737.eval a = true) (h341 : c341.eval a = true) (h384 : c384.eval a = true) (h555 : c555.eval a = true) (h21 : c21.eval a = true) (h117 : c117.eval a = true) (h382 : c382.eval a = true) : c766.eval a = true := by
  cases hc : c766.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 15, 16, 17, 87, 88, 89, 106] : Array Nat)[k]!)
    have u0 := negUnit (i := 106) (p := false) hc (by decide)
    have u1 := negUnit (i := 87) (p := true) hc (by decide)
    apply clash mini766 unsat766 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h341, (Bool.and_eq_true_iff.mpr ⟨h384, (Bool.and_eq_true_iff.mpr ⟨h555, (Bool.and_eq_true_iff.mpr ⟨h21, (Bool.and_eq_true_iff.mpr ⟨h117, (Bool.and_eq_true_iff.mpr ⟨h382, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini767 : CNF Nat := ⟨#[[(4, true)], [(0, true)], [(0, false), (1, false)], [(4, false), (5, false)], [(4, false), (8, false)], [(10, false), (5, true)], [(13, false), (8, true)], [(14, false), (8, true)], [(12, true), (13, true), (14, true)], [(9, false), (12, false)], [(9, true), (10, true), (11, true)], [(3, false), (11, false)], [(7, false), (11, false)], [(1, true), (2, true), (3, true)], [(5, true), (6, true), (7, true)], [(2, false), (6, false)]]⟩
refute_hints unsat767 mini767 16
theorem step767 (a : Nat → Bool) (h737 : c737.eval a = true) (h338 : c338.eval a = true) (h539 : c539.eval a = true) (h542 : c542.eval a = true) (h765 : c765.eval a = true) (h766 : c766.eval a = true) (h764 : c764.eval a = true) (h141 : c141.eval a = true) (h575 : c575.eval a = true) (h137 : c137.eval a = true) (h379 : c379.eval a = true) (h553 : c553.eval a = true) (h17 : c17.eval a = true) (h113 : c113.eval a = true) (h375 : c375.eval a = true) : c767.eval a = true := by
  cases hc : c767.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[0, 12, 13, 14, 81, 84, 85, 86, 87, 102, 103, 104, 105, 106, 107] : Array Nat)[k]!)
    have u0 := negUnit (i := 81) (p := false) hc (by decide)
    apply clash mini767 unsat767 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h737, (Bool.and_eq_true_iff.mpr ⟨h338, (Bool.and_eq_true_iff.mpr ⟨h539, (Bool.and_eq_true_iff.mpr ⟨h542, (Bool.and_eq_true_iff.mpr ⟨h765, (Bool.and_eq_true_iff.mpr ⟨h766, (Bool.and_eq_true_iff.mpr ⟨h764, (Bool.and_eq_true_iff.mpr ⟨h141, (Bool.and_eq_true_iff.mpr ⟨h575, (Bool.and_eq_true_iff.mpr ⟨h137, (Bool.and_eq_true_iff.mpr ⟨h379, (Bool.and_eq_true_iff.mpr ⟨h553, (Bool.and_eq_true_iff.mpr ⟨h17, (Bool.and_eq_true_iff.mpr ⟨h113, (Bool.and_eq_true_iff.mpr ⟨h375, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini768 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(2, false), (6, false)], [(0, true), (1, true), (2, true)], [(5, false), (6, false)], [(3, true), (4, true), (5, true)], [(1, false), (4, false)]]⟩
refute_hints unsat768 mini768 8
theorem step768 (a : Nat → Bool) (h433 : c433.eval a = true) (h37 : c37.eval a = true) (h583 : c583.eval a = true) (h149 : c149.eval a = true) (h429 : c429.eval a = true) : c768.eval a = true := by
  cases hc : c768.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[27, 28, 29, 111, 112, 113, 125] : Array Nat)[k]!)
    have u0 := negUnit (i := 125) (p := false) hc (by decide)
    have u1 := negUnit (i := 27) (p := true) hc (by decide)
    have u2 := negUnit (i := 111) (p := true) hc (by decide)
    apply clash mini768 unsat768 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h433, (Bool.and_eq_true_iff.mpr ⟨h37, (Bool.and_eq_true_iff.mpr ⟨h583, (Bool.and_eq_true_iff.mpr ⟨h149, (Bool.and_eq_true_iff.mpr ⟨h429, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini769 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(1, false), (6, false)], [(0, true), (1, true), (2, true)], [(4, false), (6, false)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat769 mini769 8
theorem step769 (a : Nat → Bool) (h426 : c426.eval a = true) (h33 : c33.eval a = true) (h579 : c579.eval a = true) (h145 : c145.eval a = true) (h424 : c424.eval a = true) : c769.eval a = true := by
  cases hc : c769.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[24, 25, 26, 108, 109, 110, 121] : Array Nat)[k]!)
    have u0 := negUnit (i := 121) (p := false) hc (by decide)
    have u1 := negUnit (i := 24) (p := true) hc (by decide)
    have u2 := negUnit (i := 108) (p := true) hc (by decide)
    apply clash mini769 unsat769 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h426, (Bool.and_eq_true_iff.mpr ⟨h33, (Bool.and_eq_true_iff.mpr ⟨h579, (Bool.and_eq_true_iff.mpr ⟨h145, (Bool.and_eq_true_iff.mpr ⟨h424, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini770 : CNF Nat := ⟨#[[(6, true)], [(0, false)], [(3, false)], [(1, false), (6, false)], [(4, false), (6, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat770 mini770 8
theorem step770 (a : Nat → Bool) (h432 : c432.eval a = true) (h582 : c582.eval a = true) (h37 : c37.eval a = true) (h149 : c149.eval a = true) (h430 : c430.eval a = true) : c770.eval a = true := by
  cases hc : c770.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[27, 28, 29, 111, 112, 113, 124] : Array Nat)[k]!)
    have u0 := negUnit (i := 124) (p := false) hc (by decide)
    have u1 := negUnit (i := 27) (p := true) hc (by decide)
    have u2 := negUnit (i := 111) (p := true) hc (by decide)
    apply clash mini770 unsat770 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨u2, (Bool.and_eq_true_iff.mpr ⟨h432, (Bool.and_eq_true_iff.mpr ⟨h582, (Bool.and_eq_true_iff.mpr ⟨h37, (Bool.and_eq_true_iff.mpr ⟨h149, (Bool.and_eq_true_iff.mpr ⟨h430, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini771 : CNF Nat := ⟨#[[(5, true)], [(0, true)], [(5, false), (6, false)], [(5, false), (9, false)], [(0, false), (1, false)], [(0, false), (4, false)], [(11, false), (1, true), (6, true)], [(15, false), (4, true), (9, true)], [(14, false), (4, true), (9, true)], [(13, true), (14, true), (15, true)], [(10, false), (13, false)], [(10, true), (11, true), (12, true)], [(3, false), (12, false)], [(8, false), (12, false)], [(1, true), (2, true), (3, true)], [(6, true), (7, true), (8, true)], [(2, false), (7, false)]]⟩
refute_hints unsat771 mini771 17
theorem step771 (a : Nat → Bool) (h560 : c560.eval a = true) (h563 : c563.eval a = true) (h392 : c392.eval a = true) (h395 : c395.eval a = true) (h769 : c769.eval a = true) (h768 : c768.eval a = true) (h770 : c770.eval a = true) (h165 : c165.eval a = true) (h596 : c596.eval a = true) (h161 : c161.eval a = true) (h427 : c427.eval a = true) (h580 : c580.eval a = true) (h33 : c33.eval a = true) (h145 : c145.eval a = true) (h423 : c423.eval a = true) : c771.eval a = true := by
  cases hc : c771.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 24, 25, 26, 27, 90, 108, 109, 110, 111, 120, 121, 122, 123, 124, 125] : Array Nat)[k]!)
    have u0 := negUnit (i := 90) (p := false) hc (by decide)
    have u1 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini771 unsat771 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h560, (Bool.and_eq_true_iff.mpr ⟨h563, (Bool.and_eq_true_iff.mpr ⟨h392, (Bool.and_eq_true_iff.mpr ⟨h395, (Bool.and_eq_true_iff.mpr ⟨h769, (Bool.and_eq_true_iff.mpr ⟨h768, (Bool.and_eq_true_iff.mpr ⟨h770, (Bool.and_eq_true_iff.mpr ⟨h165, (Bool.and_eq_true_iff.mpr ⟨h596, (Bool.and_eq_true_iff.mpr ⟨h161, (Bool.and_eq_true_iff.mpr ⟨h427, (Bool.and_eq_true_iff.mpr ⟨h580, (Bool.and_eq_true_iff.mpr ⟨h33, (Bool.and_eq_true_iff.mpr ⟨h145, (Bool.and_eq_true_iff.mpr ⟨h423, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini772 : CNF Nat := ⟨#[[(13, true)], [(0, true)], [(1, false)], [(4, false)], [(3, false), (0, false)], [(5, false), (0, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(2, false), (7, false)], [(6, false), (10, false)], [(9, false), (13, false)], [(7, true), (8, true), (9, true)], [(12, false), (13, false)], [(10, true), (11, true), (12, true)], [(8, false), (11, false)]]⟩
refute_hints unsat772 mini772 15
theorem step772 (a : Nat → Bool) (h757 : c757.eval a = true) (h767 : c767.eval a = true) (h761 : c761.eval a = true) (h771 : c771.eval a = true) (h753 : c753.eval a = true) (h763 : c763.eval a = true) (h530 : c530.eval a = true) (h569 : c569.eval a = true) (h595 : c595.eval a = true) (h157 : c157.eval a = true) (h613 : c613.eval a = true) (h189 : c189.eval a = true) (h591 : c591.eval a = true) : c772.eval a = true := by
  cases hc : c772.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 66, 75, 78, 81, 90, 93, 117, 118, 119, 141, 142, 143, 149] : Array Nat)[k]!)
    have u0 := negUnit (i := 149) (p := false) hc (by decide)
    have u1 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini772 unsat772 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h757, (Bool.and_eq_true_iff.mpr ⟨h767, (Bool.and_eq_true_iff.mpr ⟨h761, (Bool.and_eq_true_iff.mpr ⟨h771, (Bool.and_eq_true_iff.mpr ⟨h753, (Bool.and_eq_true_iff.mpr ⟨h763, (Bool.and_eq_true_iff.mpr ⟨h530, (Bool.and_eq_true_iff.mpr ⟨h569, (Bool.and_eq_true_iff.mpr ⟨h595, (Bool.and_eq_true_iff.mpr ⟨h157, (Bool.and_eq_true_iff.mpr ⟨h613, (Bool.and_eq_true_iff.mpr ⟨h189, (Bool.and_eq_true_iff.mpr ⟨h591, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini773 : CNF Nat := ⟨#[[(13, true)], [(0, true)], [(1, false)], [(4, false)], [(3, false), (0, false)], [(5, false), (0, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(2, false), (7, false)], [(6, false), (10, false)], [(8, false), (13, false)], [(7, true), (8, true), (9, true)], [(11, false), (13, false)], [(10, true), (11, true), (12, true)], [(9, false), (12, false)]]⟩
refute_hints unsat773 mini773 15
theorem step773 (a : Nat → Bool) (h757 : c757.eval a = true) (h767 : c767.eval a = true) (h761 : c761.eval a = true) (h771 : c771.eval a = true) (h753 : c753.eval a = true) (h763 : c763.eval a = true) (h527 : c527.eval a = true) (h566 : c566.eval a = true) (h588 : c588.eval a = true) (h153 : c153.eval a = true) (h609 : c609.eval a = true) (h185 : c185.eval a = true) (h586 : c586.eval a = true) : c773.eval a = true := by
  cases hc : c773.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 66, 75, 78, 81, 90, 93, 114, 115, 116, 138, 139, 140, 145] : Array Nat)[k]!)
    have u0 := negUnit (i := 145) (p := false) hc (by decide)
    have u1 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini773 unsat773 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h757, (Bool.and_eq_true_iff.mpr ⟨h767, (Bool.and_eq_true_iff.mpr ⟨h761, (Bool.and_eq_true_iff.mpr ⟨h771, (Bool.and_eq_true_iff.mpr ⟨h753, (Bool.and_eq_true_iff.mpr ⟨h763, (Bool.and_eq_true_iff.mpr ⟨h527, (Bool.and_eq_true_iff.mpr ⟨h566, (Bool.and_eq_true_iff.mpr ⟨h588, (Bool.and_eq_true_iff.mpr ⟨h153, (Bool.and_eq_true_iff.mpr ⟨h609, (Bool.and_eq_true_iff.mpr ⟨h185, (Bool.and_eq_true_iff.mpr ⟨h586, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini774 : CNF Nat := ⟨#[[(13, true)], [(0, true)], [(1, false)], [(4, false)], [(3, false), (0, false)], [(5, false), (0, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(8, false), (13, false)], [(11, false), (13, false)], [(2, false), (7, false)], [(6, false), (10, false)], [(7, true), (8, true), (9, true)], [(10, true), (11, true), (12, true)], [(9, false), (12, false)]]⟩
refute_hints unsat774 mini774 15
theorem step774 (a : Nat → Bool) (h757 : c757.eval a = true) (h767 : c767.eval a = true) (h761 : c761.eval a = true) (h771 : c771.eval a = true) (h753 : c753.eval a = true) (h763 : c763.eval a = true) (h594 : c594.eval a = true) (h612 : c612.eval a = true) (h530 : c530.eval a = true) (h569 : c569.eval a = true) (h157 : c157.eval a = true) (h189 : c189.eval a = true) (h592 : c592.eval a = true) : c774.eval a = true := by
  cases hc : c774.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 66, 75, 78, 81, 90, 93, 117, 118, 119, 141, 142, 143, 148] : Array Nat)[k]!)
    have u0 := negUnit (i := 148) (p := false) hc (by decide)
    have u1 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini774 unsat774 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h757, (Bool.and_eq_true_iff.mpr ⟨h767, (Bool.and_eq_true_iff.mpr ⟨h761, (Bool.and_eq_true_iff.mpr ⟨h771, (Bool.and_eq_true_iff.mpr ⟨h753, (Bool.and_eq_true_iff.mpr ⟨h763, (Bool.and_eq_true_iff.mpr ⟨h594, (Bool.and_eq_true_iff.mpr ⟨h612, (Bool.and_eq_true_iff.mpr ⟨h530, (Bool.and_eq_true_iff.mpr ⟨h569, (Bool.and_eq_true_iff.mpr ⟨h157, (Bool.and_eq_true_iff.mpr ⟨h189, (Bool.and_eq_true_iff.mpr ⟨h592, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini775 : CNF Nat := ⟨#[[(0, true)], [(1, false)], [(4, false)], [(3, false), (0, false)], [(5, false), (0, false)], [(18, false), (0, false)], [(14, false), (0, false)], [(17, false), (0, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(16, true), (17, true), (18, true)], [(2, false), (7, false)], [(6, false), (10, false)], [(13, false), (16, false)], [(13, true), (14, true), (15, true)], [(9, false), (15, false)], [(12, false), (15, false)], [(7, true), (8, true), (9, true)], [(10, true), (11, true), (12, true)], [(8, false), (11, false)]]⟩
refute_hints unsat775 mini775 20
theorem step775 (a : Nat → Bool) (h757 : c757.eval a = true) (h767 : c767.eval a = true) (h761 : c761.eval a = true) (h771 : c771.eval a = true) (h772 : c772.eval a = true) (h773 : c773.eval a = true) (h774 : c774.eval a = true) (h753 : c753.eval a = true) (h763 : c763.eval a = true) (h197 : c197.eval a = true) (h527 : c527.eval a = true) (h566 : c566.eval a = true) (h614 : c614.eval a = true) (h193 : c193.eval a = true) (h589 : c589.eval a = true) (h610 : c610.eval a = true) (h153 : c153.eval a = true) (h185 : c185.eval a = true) (h585 : c585.eval a = true) : c775.eval a = true := by
  cases hc : c775.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 66, 75, 78, 81, 90, 93, 114, 115, 116, 138, 139, 140, 144, 145, 146, 147, 148, 149] : Array Nat)[k]!)
    have u0 := negUnit (i := 21) (p := false) hc (by decide)
    apply clash mini775 unsat775 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h757, (Bool.and_eq_true_iff.mpr ⟨h767, (Bool.and_eq_true_iff.mpr ⟨h761, (Bool.and_eq_true_iff.mpr ⟨h771, (Bool.and_eq_true_iff.mpr ⟨h772, (Bool.and_eq_true_iff.mpr ⟨h773, (Bool.and_eq_true_iff.mpr ⟨h774, (Bool.and_eq_true_iff.mpr ⟨h753, (Bool.and_eq_true_iff.mpr ⟨h763, (Bool.and_eq_true_iff.mpr ⟨h197, (Bool.and_eq_true_iff.mpr ⟨h527, (Bool.and_eq_true_iff.mpr ⟨h566, (Bool.and_eq_true_iff.mpr ⟨h614, (Bool.and_eq_true_iff.mpr ⟨h193, (Bool.and_eq_true_iff.mpr ⟨h589, (Bool.and_eq_true_iff.mpr ⟨h610, (Bool.and_eq_true_iff.mpr ⟨h153, (Bool.and_eq_true_iff.mpr ⟨h185, (Bool.and_eq_true_iff.mpr ⟨h585, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini776 : CNF Nat := ⟨#[[(3, true)], [(5, false)], [(1, false)], [(0, false), (3, false)], [(0, true), (1, true), (2, true)], [(3, false), (4, false)], [(4, true), (5, true), (6, true)], [(2, false), (6, false)]]⟩
refute_hints unsat776 mini776 8
theorem step776 (a : Nat → Bool) (h743 : c743.eval a = true) (h656 : c656.eval a = true) (h221 : c221.eval a = true) (h668 : c668.eval a = true) (h237 : c237.eval a = true) (h661 : c661.eval a = true) : c776.eval a = true := by
  cases hc : c776.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[165, 166, 167, 174, 177, 178, 179] : Array Nat)[k]!)
    have u0 := negUnit (i := 174) (p := false) hc (by decide)
    have u1 := negUnit (i := 178) (p := true) hc (by decide)
    apply clash mini776 unsat776 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h743, (Bool.and_eq_true_iff.mpr ⟨h656, (Bool.and_eq_true_iff.mpr ⟨h221, (Bool.and_eq_true_iff.mpr ⟨h668, (Bool.and_eq_true_iff.mpr ⟨h237, (Bool.and_eq_true_iff.mpr ⟨h661, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini777 : CNF Nat := ⟨#[[(10, false)], [(4, false)], [(2, false)], [(0, false)], [(0, true), (1, true), (2, true)], [(1, false), (7, false)], [(6, false), (10, true)], [(6, true), (7, true), (8, true)], [(5, false), (8, false)], [(8, false), (11, false)], [(3, true), (4, true), (5, true)], [(9, true), (10, true), (11, true)], [(3, false), (9, false)]]⟩
refute_hints unsat777 mini777 13
theorem step777 (a : Nat → Bool) (h743 : c743.eval a = true) (h747 : c747.eval a = true) (h775 : c775.eval a = true) (h29 : c29.eval a = true) (h751 : c751.eval a = true) (h776 : c776.eval a = true) (h233 : c233.eval a = true) (h658 : c658.eval a = true) (h670 : c670.eval a = true) (h221 : c221.eval a = true) (h237 : c237.eval a = true) (h659 : c659.eval a = true) : c777.eval a = true := by
  cases hc : c777.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 22, 23, 165, 166, 167, 174, 175, 176, 177, 178, 179] : Array Nat)[k]!)
    have u0 := negUnit (i := 178) (p := true) hc (by decide)
    apply clash mini777 unsat777 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h743, (Bool.and_eq_true_iff.mpr ⟨h747, (Bool.and_eq_true_iff.mpr ⟨h775, (Bool.and_eq_true_iff.mpr ⟨h29, (Bool.and_eq_true_iff.mpr ⟨h751, (Bool.and_eq_true_iff.mpr ⟨h776, (Bool.and_eq_true_iff.mpr ⟨h233, (Bool.and_eq_true_iff.mpr ⟨h658, (Bool.and_eq_true_iff.mpr ⟨h670, (Bool.and_eq_true_iff.mpr ⟨h221, (Bool.and_eq_true_iff.mpr ⟨h237, (Bool.and_eq_true_iff.mpr ⟨h659, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini778 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(3, false), (7, false)], [(1, true), (2, true), (3, true)], [(6, false), (7, false)], [(4, true), (5, true), (6, true)], [(1, false), (4, false)]]⟩
refute_hints unsat778 mini778 9
theorem step778 (a : Nat → Bool) (h738 : c738.eval a = true) (h354 : c354.eval a = true) (h493 : c493.eval a = true) (h77 : c77.eval a = true) (h634 : c634.eval a = true) (h209 : c209.eval a = true) (h488 : c488.eval a = true) : c778.eval a = true := by
  cases hc : c778.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 57, 58, 59, 156, 157, 158, 197] : Array Nat)[k]!)
    have u0 := negUnit (i := 197) (p := false) hc (by decide)
    have u1 := negUnit (i := 157) (p := true) hc (by decide)
    apply clash mini778 unsat778 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h354, (Bool.and_eq_true_iff.mpr ⟨h493, (Bool.and_eq_true_iff.mpr ⟨h77, (Bool.and_eq_true_iff.mpr ⟨h634, (Bool.and_eq_true_iff.mpr ⟨h209, (Bool.and_eq_true_iff.mpr ⟨h488, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini779 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(1, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, false), (7, false)], [(4, true), (5, true), (6, true)], [(3, false), (6, false)]]⟩
refute_hints unsat779 mini779 9
theorem step779 (a : Nat → Bool) (h738 : c738.eval a = true) (h351 : c351.eval a = true) (h485 : c485.eval a = true) (h73 : c73.eval a = true) (h629 : c629.eval a = true) (h205 : c205.eval a = true) (h484 : c484.eval a = true) : c779.eval a = true := by
  cases hc : c779.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 54, 55, 56, 153, 154, 155, 192] : Array Nat)[k]!)
    have u0 := negUnit (i := 192) (p := false) hc (by decide)
    have u1 := negUnit (i := 154) (p := true) hc (by decide)
    apply clash mini779 unsat779 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h351, (Bool.and_eq_true_iff.mpr ⟨h485, (Bool.and_eq_true_iff.mpr ⟨h73, (Bool.and_eq_true_iff.mpr ⟨h629, (Bool.and_eq_true_iff.mpr ⟨h205, (Bool.and_eq_true_iff.mpr ⟨h484, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini780 : CNF Nat := ⟨#[[(7, true)], [(5, false)], [(0, true)], [(0, false), (2, false)], [(3, false), (7, false)], [(6, false), (7, false)], [(1, true), (2, true), (3, true)], [(4, true), (5, true), (6, true)], [(1, false), (4, false)]]⟩
refute_hints unsat780 mini780 9
theorem step780 (a : Nat → Bool) (h738 : c738.eval a = true) (h351 : c351.eval a = true) (h487 : c487.eval a = true) (h631 : c631.eval a = true) (h73 : c73.eval a = true) (h205 : c205.eval a = true) (h482 : c482.eval a = true) : c780.eval a = true := by
  cases hc : c780.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 54, 55, 56, 153, 154, 155, 194] : Array Nat)[k]!)
    have u0 := negUnit (i := 194) (p := false) hc (by decide)
    have u1 := negUnit (i := 154) (p := true) hc (by decide)
    apply clash mini780 unsat780 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h351, (Bool.and_eq_true_iff.mpr ⟨h487, (Bool.and_eq_true_iff.mpr ⟨h631, (Bool.and_eq_true_iff.mpr ⟨h73, (Bool.and_eq_true_iff.mpr ⟨h205, (Bool.and_eq_true_iff.mpr ⟨h482, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini781 : CNF Nat := ⟨#[[(4, true)], [(0, true)], [(0, false), (2, false)], [(4, false), (5, false)], [(4, false), (7, false)], [(11, false), (5, true)], [(9, false), (5, true)], [(14, false), (7, true)], [(9, true), (10, true), (11, true)], [(10, false), (13, false)], [(12, true), (13, true), (14, true)], [(1, false), (12, false)], [(6, false), (12, false)], [(1, true), (2, true), (3, true)], [(6, true), (7, true), (8, true)], [(3, false), (8, false)]]⟩
refute_hints unsat781 mini781 16
theorem step781 (a : Nat → Bool) (h738 : c738.eval a = true) (h354 : c354.eval a = true) (h618 : c618.eval a = true) (h621 : c621.eval a = true) (h780 : c780.eval a = true) (h779 : c779.eval a = true) (h778 : c778.eval a = true) (h257 : c257.eval a = true) (h693 : c693.eval a = true) (h261 : c261.eval a = true) (h491 : c491.eval a = true) (h632 : c632.eval a = true) (h77 : c77.eval a = true) (h209 : c209.eval a = true) (h490 : c490.eval a = true) : c781.eval a = true := by
  cases hc : c781.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[4, 57, 58, 59, 151, 154, 156, 157, 158, 192, 193, 194, 195, 196, 197] : Array Nat)[k]!)
    have u0 := negUnit (i := 151) (p := false) hc (by decide)
    apply clash mini781 unsat781 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h738, (Bool.and_eq_true_iff.mpr ⟨h354, (Bool.and_eq_true_iff.mpr ⟨h618, (Bool.and_eq_true_iff.mpr ⟨h621, (Bool.and_eq_true_iff.mpr ⟨h780, (Bool.and_eq_true_iff.mpr ⟨h779, (Bool.and_eq_true_iff.mpr ⟨h778, (Bool.and_eq_true_iff.mpr ⟨h257, (Bool.and_eq_true_iff.mpr ⟨h693, (Bool.and_eq_true_iff.mpr ⟨h261, (Bool.and_eq_true_iff.mpr ⟨h491, (Bool.and_eq_true_iff.mpr ⟨h632, (Bool.and_eq_true_iff.mpr ⟨h77, (Bool.and_eq_true_iff.mpr ⟨h209, (Bool.and_eq_true_iff.mpr ⟨h490, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini782 : CNF Nat := ⟨#[[(9, true)], [(7, false)], [(2, false)], [(0, false)], [(0, true), (1, true), (2, true)], [(1, false), (4, false)], [(5, false), (9, false)], [(3, true), (4, true), (5, true)], [(8, false), (9, false)], [(6, true), (7, true), (8, true)], [(3, false), (6, false)]]⟩
refute_hints unsat782 mini782 11
theorem step782 (a : Nat → Bool) (h747 : c747.eval a = true) (h775 : c775.eval a = true) (h29 : c29.eval a = true) (h420 : c420.eval a = true) (h481 : c481.eval a = true) (h69 : c69.eval a = true) (h724 : c724.eval a = true) (h301 : c301.eval a = true) (h476 : c476.eval a = true) : c782.eval a = true := by
  cases hc : c782.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 22, 23, 51, 52, 53, 225, 226, 227, 233] : Array Nat)[k]!)
    have u0 := negUnit (i := 233) (p := false) hc (by decide)
    have u1 := negUnit (i := 226) (p := true) hc (by decide)
    apply clash mini782 unsat782 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h747, (Bool.and_eq_true_iff.mpr ⟨h775, (Bool.and_eq_true_iff.mpr ⟨h29, (Bool.and_eq_true_iff.mpr ⟨h420, (Bool.and_eq_true_iff.mpr ⟨h481, (Bool.and_eq_true_iff.mpr ⟨h69, (Bool.and_eq_true_iff.mpr ⟨h724, (Bool.and_eq_true_iff.mpr ⟨h301, (Bool.and_eq_true_iff.mpr ⟨h476, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini783 : CNF Nat := ⟨#[[(9, true)], [(7, false)], [(2, false)], [(0, false)], [(0, true), (1, true), (2, true)], [(1, false), (4, false)], [(3, false), (9, false)], [(3, true), (4, true), (5, true)], [(6, false), (9, false)], [(6, true), (7, true), (8, true)], [(5, false), (8, false)]]⟩
refute_hints unsat783 mini783 11
theorem step783 (a : Nat → Bool) (h747 : c747.eval a = true) (h775 : c775.eval a = true) (h29 : c29.eval a = true) (h417 : c417.eval a = true) (h473 : c473.eval a = true) (h65 : c65.eval a = true) (h719 : c719.eval a = true) (h297 : c297.eval a = true) (h472 : c472.eval a = true) : c783.eval a = true := by
  cases hc : c783.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 22, 23, 48, 49, 50, 222, 223, 224, 228] : Array Nat)[k]!)
    have u0 := negUnit (i := 228) (p := false) hc (by decide)
    have u1 := negUnit (i := 223) (p := true) hc (by decide)
    apply clash mini783 unsat783 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h747, (Bool.and_eq_true_iff.mpr ⟨h775, (Bool.and_eq_true_iff.mpr ⟨h29, (Bool.and_eq_true_iff.mpr ⟨h417, (Bool.and_eq_true_iff.mpr ⟨h473, (Bool.and_eq_true_iff.mpr ⟨h65, (Bool.and_eq_true_iff.mpr ⟨h719, (Bool.and_eq_true_iff.mpr ⟨h297, (Bool.and_eq_true_iff.mpr ⟨h472, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini784 : CNF Nat := ⟨#[[(9, true)], [(7, false)], [(2, false)], [(0, false)], [(0, true), (1, true), (2, true)], [(1, false), (4, false)], [(5, false), (9, false)], [(8, false), (9, false)], [(3, true), (4, true), (5, true)], [(6, true), (7, true), (8, true)], [(3, false), (6, false)]]⟩
refute_hints unsat784 mini784 11
theorem step784 (a : Nat → Bool) (h747 : c747.eval a = true) (h775 : c775.eval a = true) (h29 : c29.eval a = true) (h417 : c417.eval a = true) (h475 : c475.eval a = true) (h721 : c721.eval a = true) (h65 : c65.eval a = true) (h297 : c297.eval a = true) (h470 : c470.eval a = true) : c784.eval a = true := by
  cases hc : c784.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 22, 23, 48, 49, 50, 222, 223, 224, 230] : Array Nat)[k]!)
    have u0 := negUnit (i := 230) (p := false) hc (by decide)
    have u1 := negUnit (i := 223) (p := true) hc (by decide)
    apply clash mini784 unsat784 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h747, (Bool.and_eq_true_iff.mpr ⟨h775, (Bool.and_eq_true_iff.mpr ⟨h29, (Bool.and_eq_true_iff.mpr ⟨h417, (Bool.and_eq_true_iff.mpr ⟨h475, (Bool.and_eq_true_iff.mpr ⟨h721, (Bool.and_eq_true_iff.mpr ⟨h65, (Bool.and_eq_true_iff.mpr ⟨h297, (Bool.and_eq_true_iff.mpr ⟨h470, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini785 : CNF Nat := ⟨#[[(6, true)], [(2, false)], [(0, false)], [(0, true), (1, true), (2, true)], [(1, false), (4, false)], [(6, false), (7, false)], [(6, false), (9, false)], [(13, false), (7, true)], [(11, false), (7, true)], [(16, false), (9, true)], [(11, true), (12, true), (13, true)], [(12, false), (15, false)], [(14, true), (15, true), (16, true)], [(3, false), (14, false)], [(8, false), (14, false)], [(3, true), (4, true), (5, true)], [(8, true), (9, true), (10, true)], [(5, false), (10, false)]]⟩
refute_hints unsat785 mini785 18
theorem step785 (a : Nat → Bool) (h747 : c747.eval a = true) (h775 : c775.eval a = true) (h29 : c29.eval a = true) (h420 : c420.eval a = true) (h645 : c645.eval a = true) (h648 : c648.eval a = true) (h784 : c784.eval a = true) (h783 : c783.eval a = true) (h782 : c782.eval a = true) (h305 : c305.eval a = true) (h726 : c726.eval a = true) (h309 : c309.eval a = true) (h479 : c479.eval a = true) (h722 : c722.eval a = true) (h69 : c69.eval a = true) (h301 : c301.eval a = true) (h478 : c478.eval a = true) : c785.eval a = true := by
  cases hc : c785.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[21, 22, 23, 51, 52, 53, 163, 223, 225, 226, 227, 228, 229, 230, 231, 232, 233] : Array Nat)[k]!)
    have u0 := negUnit (i := 163) (p := false) hc (by decide)
    apply clash mini785 unsat785 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h747, (Bool.and_eq_true_iff.mpr ⟨h775, (Bool.and_eq_true_iff.mpr ⟨h29, (Bool.and_eq_true_iff.mpr ⟨h420, (Bool.and_eq_true_iff.mpr ⟨h645, (Bool.and_eq_true_iff.mpr ⟨h648, (Bool.and_eq_true_iff.mpr ⟨h784, (Bool.and_eq_true_iff.mpr ⟨h783, (Bool.and_eq_true_iff.mpr ⟨h782, (Bool.and_eq_true_iff.mpr ⟨h305, (Bool.and_eq_true_iff.mpr ⟨h726, (Bool.and_eq_true_iff.mpr ⟨h309, (Bool.and_eq_true_iff.mpr ⟨h479, (Bool.and_eq_true_iff.mpr ⟨h722, (Bool.and_eq_true_iff.mpr ⟨h69, (Bool.and_eq_true_iff.mpr ⟨h301, (Bool.and_eq_true_iff.mpr ⟨h478, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini786 : CNF Nat := ⟨#[[(6, true)], [(4, false)], [(1, false)], [(2, false), (6, false)], [(0, true), (1, true), (2, true)], [(5, false), (6, false)], [(3, true), (4, true), (5, true)], [(0, false), (3, false)]]⟩
refute_hints unsat786 mini786 8
theorem step786 (a : Nat → Bool) (h781 : c781.eval a = true) (h628 : c628.eval a = true) (h201 : c201.eval a = true) (h637 : c637.eval a = true) (h213 : c213.eval a = true) (h623 : c623.eval a = true) : c786.eval a = true := by
  cases hc : c786.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[150, 151, 152, 159, 160, 161, 164] : Array Nat)[k]!)
    have u0 := negUnit (i := 164) (p := false) hc (by decide)
    have u1 := negUnit (i := 160) (p := true) hc (by decide)
    apply clash mini786 unsat786 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨u1, (Bool.and_eq_true_iff.mpr ⟨h781, (Bool.and_eq_true_iff.mpr ⟨h628, (Bool.and_eq_true_iff.mpr ⟨h201, (Bool.and_eq_true_iff.mpr ⟨h637, (Bool.and_eq_true_iff.mpr ⟨h213, (Bool.and_eq_true_iff.mpr ⟨h623, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini787 : CNF Nat := ⟨#[[(4, false)], [(1, false)], [(7, false)], [(8, false), (4, true)], [(6, true), (7, true), (8, true)], [(0, false), (6, false)], [(3, false), (6, false)], [(0, true), (1, true), (2, true)], [(3, true), (4, true), (5, true)], [(2, false), (5, false)]]⟩
refute_hints unsat787 mini787 10
theorem step787 (a : Nat → Bool) (h781 : c781.eval a = true) (h785 : c785.eval a = true) (h786 : c786.eval a = true) (h217 : c217.eval a = true) (h626 : c626.eval a = true) (h635 : c635.eval a = true) (h201 : c201.eval a = true) (h213 : c213.eval a = true) (h625 : c625.eval a = true) : c787.eval a = true := by
  cases hc : c787.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[150, 151, 152, 159, 160, 161, 162, 163, 164] : Array Nat)[k]!)
    have u0 := negUnit (i := 160) (p := true) hc (by decide)
    apply clash mini787 unsat787 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h781, (Bool.and_eq_true_iff.mpr ⟨h785, (Bool.and_eq_true_iff.mpr ⟨h786, (Bool.and_eq_true_iff.mpr ⟨h217, (Bool.and_eq_true_iff.mpr ⟨h626, (Bool.and_eq_true_iff.mpr ⟨h635, (Bool.and_eq_true_iff.mpr ⟨h201, (Bool.and_eq_true_iff.mpr ⟨h213, (Bool.and_eq_true_iff.mpr ⟨h625, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini788 : CNF Nat := ⟨#[[(8, true)], [(1, true)], [(1, false), (6, false)], [(0, true)], [(0, false), (3, false)], [(4, false), (8, false)], [(2, true), (3, true), (4, true)], [(7, false), (8, false)], [(5, true), (6, true), (7, true)], [(2, false), (5, false)]]⟩
refute_hints unsat788 mini788 10
theorem step788 (a : Nat → Bool) (h777 : c777.eval a = true) (h681 : c681.eval a = true) (h787 : c787.eval a = true) (h642 : c642.eval a = true) (h715 : c715.eval a = true) (h285 : c285.eval a = true) (h733 : c733.eval a = true) (h317 : c317.eval a = true) (h710 : c710.eval a = true) : c788.eval a = true := by
  cases hc : c788.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[160, 178, 213, 214, 215, 237, 238, 239, 245] : Array Nat)[k]!)
    have u0 := negUnit (i := 245) (p := false) hc (by decide)
    apply clash mini788 unsat788 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h777, (Bool.and_eq_true_iff.mpr ⟨h681, (Bool.and_eq_true_iff.mpr ⟨h787, (Bool.and_eq_true_iff.mpr ⟨h642, (Bool.and_eq_true_iff.mpr ⟨h715, (Bool.and_eq_true_iff.mpr ⟨h285, (Bool.and_eq_true_iff.mpr ⟨h733, (Bool.and_eq_true_iff.mpr ⟨h317, (Bool.and_eq_true_iff.mpr ⟨h710, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini789 : CNF Nat := ⟨#[[(8, true)], [(1, true)], [(1, false), (6, false)], [(0, true)], [(0, false), (3, false)], [(2, false), (8, false)], [(5, false), (8, false)], [(2, true), (3, true), (4, true)], [(5, true), (6, true), (7, true)], [(4, false), (7, false)]]⟩
refute_hints unsat789 mini789 10
theorem step789 (a : Nat → Bool) (h777 : c777.eval a = true) (h681 : c681.eval a = true) (h787 : c787.eval a = true) (h642 : c642.eval a = true) (h713 : c713.eval a = true) (h731 : c731.eval a = true) (h285 : c285.eval a = true) (h317 : c317.eval a = true) (h712 : c712.eval a = true) : c789.eval a = true := by
  cases hc : c789.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[160, 178, 213, 214, 215, 237, 238, 239, 243] : Array Nat)[k]!)
    have u0 := negUnit (i := 243) (p := false) hc (by decide)
    apply clash mini789 unsat789 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h777, (Bool.and_eq_true_iff.mpr ⟨h681, (Bool.and_eq_true_iff.mpr ⟨h787, (Bool.and_eq_true_iff.mpr ⟨h642, (Bool.and_eq_true_iff.mpr ⟨h713, (Bool.and_eq_true_iff.mpr ⟨h731, (Bool.and_eq_true_iff.mpr ⟨h285, (Bool.and_eq_true_iff.mpr ⟨h317, (Bool.and_eq_true_iff.mpr ⟨h712, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini790 : CNF Nat := ⟨#[[(8, true)], [(1, true)], [(1, false), (6, false)], [(0, true)], [(0, false), (3, false)], [(2, false), (8, false)], [(2, true), (3, true), (4, true)], [(5, false), (8, false)], [(5, true), (6, true), (7, true)], [(4, false), (7, false)]]⟩
refute_hints unsat790 mini790 10
theorem step790 (a : Nat → Bool) (h777 : c777.eval a = true) (h678 : c678.eval a = true) (h787 : c787.eval a = true) (h639 : c639.eval a = true) (h707 : c707.eval a = true) (h281 : c281.eval a = true) (h728 : c728.eval a = true) (h313 : c313.eval a = true) (h706 : c706.eval a = true) : c790.eval a = true := by
  cases hc : c790.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[160, 178, 210, 211, 212, 234, 235, 236, 240] : Array Nat)[k]!)
    have u0 := negUnit (i := 240) (p := false) hc (by decide)
    apply clash mini790 unsat790 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨u0, (Bool.and_eq_true_iff.mpr ⟨h777, (Bool.and_eq_true_iff.mpr ⟨h678, (Bool.and_eq_true_iff.mpr ⟨h787, (Bool.and_eq_true_iff.mpr ⟨h639, (Bool.and_eq_true_iff.mpr ⟨h707, (Bool.and_eq_true_iff.mpr ⟨h281, (Bool.and_eq_true_iff.mpr ⟨h728, (Bool.and_eq_true_iff.mpr ⟨h313, (Bool.and_eq_true_iff.mpr ⟨h706, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
private def mini791 : CNF Nat := ⟨#[[(1, true)], [(1, false), (6, false)], [(0, true)], [(0, false), (3, false)], [(13, false)], [(11, false)], [(11, true), (12, true), (13, true)], [(9, false), (12, false)], [(8, false)], [(8, true), (9, true), (10, true)], [(4, false), (10, false)], [(7, false), (10, false)], [(2, true), (3, true), (4, true)], [(5, true), (6, true), (7, true)], [(2, false), (5, false)]]⟩
refute_hints unsat791 mini791 15
theorem step791 (a : Nat → Bool) (h777 : c777.eval a = true) (h678 : c678.eval a = true) (h787 : c787.eval a = true) (h639 : c639.eval a = true) (h788 : c788.eval a = true) (h789 : c789.eval a = true) (h325 : c325.eval a = true) (h735 : c735.eval a = true) (h790 : c790.eval a = true) (h321 : c321.eval a = true) (h709 : c709.eval a = true) (h730 : c730.eval a = true) (h281 : c281.eval a = true) (h313 : c313.eval a = true) (h704 : c704.eval a = true) : c791.eval a = true := by
  cases hc : c791.eval a with
  | true => rfl
  | false =>
    exfalso
    let b : Nat → Bool := fun k => a ((#[160, 178, 210, 211, 212, 234, 235, 236, 240, 241, 242, 243, 244, 245] : Array Nat)[k]!)
    apply clash mini791 unsat791 b
    rw [CNF.eval, ← Array.all_toList]
    exact (Bool.and_eq_true_iff.mpr ⟨h777, (Bool.and_eq_true_iff.mpr ⟨h678, (Bool.and_eq_true_iff.mpr ⟨h787, (Bool.and_eq_true_iff.mpr ⟨h639, (Bool.and_eq_true_iff.mpr ⟨h788, (Bool.and_eq_true_iff.mpr ⟨h789, (Bool.and_eq_true_iff.mpr ⟨h325, (Bool.and_eq_true_iff.mpr ⟨h735, (Bool.and_eq_true_iff.mpr ⟨h790, (Bool.and_eq_true_iff.mpr ⟨h321, (Bool.and_eq_true_iff.mpr ⟨h709, (Bool.and_eq_true_iff.mpr ⟨h730, (Bool.and_eq_true_iff.mpr ⟨h281, (Bool.and_eq_true_iff.mpr ⟨h313, (Bool.and_eq_true_iff.mpr ⟨h704, rfl⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)⟩)
def pieceInput : CNF Nat := ⟨#[c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, c62, c63, c64, c65, c66, c67, c68, c69, c70, c71, c72, c73, c74, c75, c76, c77, c78, c79, c80, c81, c82, c83, c84, c85, c86, c87, c88, c89, c90, c91, c92, c93, c94, c95, c96, c97, c98, c99, c100, c101, c102, c103, c104, c105, c106, c107, c108, c109, c110, c111, c112, c113, c114, c115, c116, c117, c118, c119, c120, c121, c122, c123, c124, c125, c126, c127, c128, c129, c130, c131, c132, c133, c134, c135, c136, c137, c138, c139, c140, c141, c142, c143, c144, c145, c146, c147, c148, c149, c150, c151, c152, c153, c154, c155, c156, c157, c158, c159, c160, c161, c162, c163, c164, c165, c166, c167, c168, c169, c170, c171, c172, c173, c174, c175, c176, c177, c178, c179, c180, c181, c182, c183, c184, c185, c186, c187, c188, c189, c190, c191, c192, c193, c194, c195, c196, c197, c198, c199, c200, c201, c202, c203, c204, c205, c206, c207, c208, c209, c210, c211, c212, c213, c214, c215, c216, c217, c218, c219, c220, c221, c222, c223, c224, c225, c226, c227, c228, c229, c230, c231, c232, c233, c234, c235, c236, c237, c238, c239, c240, c241, c242, c243, c244, c245, c246, c247, c248, c249, c250, c251, c252, c253, c254, c255, c256, c257, c258, c259, c260, c261, c262, c263, c264, c265, c266, c267, c268, c269, c270, c271, c272, c273, c274, c275, c276, c277, c278, c279, c280, c281, c282, c283, c284, c285, c286, c287, c288, c289, c290, c291, c292, c293, c294, c295, c296, c297, c298, c299, c300, c301, c302, c303, c304, c305, c306, c307, c308, c309, c310, c311, c312, c313, c314, c315, c316, c317, c318, c319, c320, c321, c322, c323, c324, c325, c326, c327, c328, c329, c330, c331, c332, c333, c334, c335, c336, c337, c338, c339, c340, c341, c342, c343, c344, c345, c346, c347, c348, c349, c350, c351, c352, c353, c354, c355, c356, c357, c358, c359, c360, c361, c362, c363, c364, c365, c366, c367, c368, c369, c370, c371, c372, c373, c374, c375, c376, c377, c378, c379, c380, c381, c382, c383, c384, c385, c386, c387, c388, c389, c390, c391, c392, c393, c394, c395, c396, c397, c398, c399, c400, c401, c402, c403, c404, c405, c406, c407, c408, c409, c410, c411, c412, c413, c414, c415, c416, c417, c418, c419, c420, c421, c422, c423, c424, c425, c426, c427, c428, c429, c430, c431, c432, c433, c434, c435, c436, c437, c438, c439, c440, c441, c442, c443, c444, c445, c446, c447, c448, c449, c450, c451, c452, c453, c454, c455, c456, c457, c458, c459, c460, c461, c462, c463, c464, c465, c466, c467, c468, c469, c470, c471, c472, c473, c474, c475, c476, c477, c478, c479, c480, c481, c482, c483, c484, c485, c486, c487, c488, c489, c490, c491, c492, c493, c494, c495, c496, c497, c498, c499, c500, c501, c502, c503, c504, c505, c506, c507, c508, c509, c510, c511, c512, c513, c514, c515, c516, c517, c518, c519, c520, c521, c522, c523, c524, c525, c526, c527, c528, c529, c530, c531, c532, c533, c534, c535, c536, c537, c538, c539, c540, c541, c542, c543, c544, c545, c546, c547, c548, c549, c550, c551, c552, c553, c554, c555, c556, c557, c558, c559, c560, c561, c562, c563, c564, c565, c566, c567, c568, c569, c570, c571, c572, c573, c574, c575, c576, c577, c578, c579, c580, c581, c582, c583, c584, c585, c586, c587, c588, c589, c590, c591, c592, c593, c594, c595, c596, c597, c598, c599, c600, c601, c602, c603, c604, c605, c606, c607, c608, c609, c610, c611, c612, c613, c614, c615, c616, c617, c618, c619, c620, c621, c622, c623, c624, c625, c626, c627, c628, c629, c630, c631, c632, c633, c634, c635, c636, c637, c638, c639, c640, c641, c642, c643, c644, c645, c646, c647, c648, c649, c650, c651, c652, c653, c654, c655, c656, c657, c658, c659, c660, c661, c662, c663, c664, c665, c666, c667, c668, c669, c670, c671, c672, c673, c674, c675, c676, c677, c678, c679, c680, c681, c682, c683, c684, c685, c686, c687, c688, c689, c690, c691, c692, c693, c694, c695, c696, c697, c698, c699, c700, c701, c702, c703, c704, c705, c706, c707, c708, c709, c710, c711, c712, c713, c714, c715, c716, c717, c718, c719, c720, c721, c722, c723, c724, c725, c726, c727, c728, c729, c730, c731, c732, c733, c734, c735, c736, c737, c738, c739]⟩
theorem pieces_unsat : pieceInput.Unsat := by
  intro a
  cases h : pieceInput.eval a with
  | false => rfl
  | true =>
    exfalso
    have h9 : c9.eval a = true := atClause pieceInput h 8 (by decide)
    have h13 : c13.eval a = true := atClause pieceInput h 12 (by decide)
    have h17 : c17.eval a = true := atClause pieceInput h 16 (by decide)
    have h21 : c21.eval a = true := atClause pieceInput h 20 (by decide)
    have h29 : c29.eval a = true := atClause pieceInput h 28 (by decide)
    have h33 : c33.eval a = true := atClause pieceInput h 32 (by decide)
    have h37 : c37.eval a = true := atClause pieceInput h 36 (by decide)
    have h41 : c41.eval a = true := atClause pieceInput h 40 (by decide)
    have h45 : c45.eval a = true := atClause pieceInput h 44 (by decide)
    have h49 : c49.eval a = true := atClause pieceInput h 48 (by decide)
    have h53 : c53.eval a = true := atClause pieceInput h 52 (by decide)
    have h57 : c57.eval a = true := atClause pieceInput h 56 (by decide)
    have h61 : c61.eval a = true := atClause pieceInput h 60 (by decide)
    have h65 : c65.eval a = true := atClause pieceInput h 64 (by decide)
    have h69 : c69.eval a = true := atClause pieceInput h 68 (by decide)
    have h73 : c73.eval a = true := atClause pieceInput h 72 (by decide)
    have h77 : c77.eval a = true := atClause pieceInput h 76 (by decide)
    have h81 : c81.eval a = true := atClause pieceInput h 80 (by decide)
    have h85 : c85.eval a = true := atClause pieceInput h 84 (by decide)
    have h89 : c89.eval a = true := atClause pieceInput h 88 (by decide)
    have h93 : c93.eval a = true := atClause pieceInput h 92 (by decide)
    have h97 : c97.eval a = true := atClause pieceInput h 96 (by decide)
    have h101 : c101.eval a = true := atClause pieceInput h 100 (by decide)
    have h105 : c105.eval a = true := atClause pieceInput h 104 (by decide)
    have h109 : c109.eval a = true := atClause pieceInput h 108 (by decide)
    have h113 : c113.eval a = true := atClause pieceInput h 112 (by decide)
    have h117 : c117.eval a = true := atClause pieceInput h 116 (by decide)
    have h121 : c121.eval a = true := atClause pieceInput h 120 (by decide)
    have h125 : c125.eval a = true := atClause pieceInput h 124 (by decide)
    have h129 : c129.eval a = true := atClause pieceInput h 128 (by decide)
    have h133 : c133.eval a = true := atClause pieceInput h 132 (by decide)
    have h137 : c137.eval a = true := atClause pieceInput h 136 (by decide)
    have h141 : c141.eval a = true := atClause pieceInput h 140 (by decide)
    have h145 : c145.eval a = true := atClause pieceInput h 144 (by decide)
    have h149 : c149.eval a = true := atClause pieceInput h 148 (by decide)
    have h153 : c153.eval a = true := atClause pieceInput h 152 (by decide)
    have h157 : c157.eval a = true := atClause pieceInput h 156 (by decide)
    have h161 : c161.eval a = true := atClause pieceInput h 160 (by decide)
    have h165 : c165.eval a = true := atClause pieceInput h 164 (by decide)
    have h169 : c169.eval a = true := atClause pieceInput h 168 (by decide)
    have h173 : c173.eval a = true := atClause pieceInput h 172 (by decide)
    have h177 : c177.eval a = true := atClause pieceInput h 176 (by decide)
    have h181 : c181.eval a = true := atClause pieceInput h 180 (by decide)
    have h185 : c185.eval a = true := atClause pieceInput h 184 (by decide)
    have h189 : c189.eval a = true := atClause pieceInput h 188 (by decide)
    have h193 : c193.eval a = true := atClause pieceInput h 192 (by decide)
    have h197 : c197.eval a = true := atClause pieceInput h 196 (by decide)
    have h201 : c201.eval a = true := atClause pieceInput h 200 (by decide)
    have h205 : c205.eval a = true := atClause pieceInput h 204 (by decide)
    have h209 : c209.eval a = true := atClause pieceInput h 208 (by decide)
    have h213 : c213.eval a = true := atClause pieceInput h 212 (by decide)
    have h217 : c217.eval a = true := atClause pieceInput h 216 (by decide)
    have h221 : c221.eval a = true := atClause pieceInput h 220 (by decide)
    have h225 : c225.eval a = true := atClause pieceInput h 224 (by decide)
    have h229 : c229.eval a = true := atClause pieceInput h 228 (by decide)
    have h233 : c233.eval a = true := atClause pieceInput h 232 (by decide)
    have h237 : c237.eval a = true := atClause pieceInput h 236 (by decide)
    have h241 : c241.eval a = true := atClause pieceInput h 240 (by decide)
    have h245 : c245.eval a = true := atClause pieceInput h 244 (by decide)
    have h249 : c249.eval a = true := atClause pieceInput h 248 (by decide)
    have h253 : c253.eval a = true := atClause pieceInput h 252 (by decide)
    have h257 : c257.eval a = true := atClause pieceInput h 256 (by decide)
    have h261 : c261.eval a = true := atClause pieceInput h 260 (by decide)
    have h265 : c265.eval a = true := atClause pieceInput h 264 (by decide)
    have h269 : c269.eval a = true := atClause pieceInput h 268 (by decide)
    have h273 : c273.eval a = true := atClause pieceInput h 272 (by decide)
    have h277 : c277.eval a = true := atClause pieceInput h 276 (by decide)
    have h281 : c281.eval a = true := atClause pieceInput h 280 (by decide)
    have h285 : c285.eval a = true := atClause pieceInput h 284 (by decide)
    have h289 : c289.eval a = true := atClause pieceInput h 288 (by decide)
    have h293 : c293.eval a = true := atClause pieceInput h 292 (by decide)
    have h297 : c297.eval a = true := atClause pieceInput h 296 (by decide)
    have h301 : c301.eval a = true := atClause pieceInput h 300 (by decide)
    have h305 : c305.eval a = true := atClause pieceInput h 304 (by decide)
    have h309 : c309.eval a = true := atClause pieceInput h 308 (by decide)
    have h313 : c313.eval a = true := atClause pieceInput h 312 (by decide)
    have h317 : c317.eval a = true := atClause pieceInput h 316 (by decide)
    have h321 : c321.eval a = true := atClause pieceInput h 320 (by decide)
    have h325 : c325.eval a = true := atClause pieceInput h 324 (by decide)
    have h332 : c332.eval a = true := atClause pieceInput h 331 (by decide)
    have h335 : c335.eval a = true := atClause pieceInput h 334 (by decide)
    have h338 : c338.eval a = true := atClause pieceInput h 337 (by decide)
    have h341 : c341.eval a = true := atClause pieceInput h 340 (by decide)
    have h351 : c351.eval a = true := atClause pieceInput h 350 (by decide)
    have h354 : c354.eval a = true := atClause pieceInput h 353 (by decide)
    have h357 : c357.eval a = true := atClause pieceInput h 356 (by decide)
    have h360 : c360.eval a = true := atClause pieceInput h 359 (by decide)
    have h363 : c363.eval a = true := atClause pieceInput h 362 (by decide)
    have h364 : c364.eval a = true := atClause pieceInput h 363 (by decide)
    have h366 : c366.eval a = true := atClause pieceInput h 365 (by decide)
    have h367 : c367.eval a = true := atClause pieceInput h 366 (by decide)
    have h369 : c369.eval a = true := atClause pieceInput h 368 (by decide)
    have h370 : c370.eval a = true := atClause pieceInput h 369 (by decide)
    have h372 : c372.eval a = true := atClause pieceInput h 371 (by decide)
    have h373 : c373.eval a = true := atClause pieceInput h 372 (by decide)
    have h375 : c375.eval a = true := atClause pieceInput h 374 (by decide)
    have h376 : c376.eval a = true := atClause pieceInput h 375 (by decide)
    have h378 : c378.eval a = true := atClause pieceInput h 377 (by decide)
    have h379 : c379.eval a = true := atClause pieceInput h 378 (by decide)
    have h381 : c381.eval a = true := atClause pieceInput h 380 (by decide)
    have h382 : c382.eval a = true := atClause pieceInput h 381 (by decide)
    have h384 : c384.eval a = true := atClause pieceInput h 383 (by decide)
    have h385 : c385.eval a = true := atClause pieceInput h 384 (by decide)
    have h388 : c388.eval a = true := atClause pieceInput h 387 (by decide)
    have h391 : c391.eval a = true := atClause pieceInput h 390 (by decide)
    have h392 : c392.eval a = true := atClause pieceInput h 391 (by decide)
    have h395 : c395.eval a = true := atClause pieceInput h 394 (by decide)
    have h398 : c398.eval a = true := atClause pieceInput h 397 (by decide)
    have h401 : c401.eval a = true := atClause pieceInput h 400 (by decide)
    have h406 : c406.eval a = true := atClause pieceInput h 405 (by decide)
    have h409 : c409.eval a = true := atClause pieceInput h 408 (by decide)
    have h411 : c411.eval a = true := atClause pieceInput h 410 (by decide)
    have h414 : c414.eval a = true := atClause pieceInput h 413 (by decide)
    have h417 : c417.eval a = true := atClause pieceInput h 416 (by decide)
    have h420 : c420.eval a = true := atClause pieceInput h 419 (by decide)
    have h423 : c423.eval a = true := atClause pieceInput h 422 (by decide)
    have h424 : c424.eval a = true := atClause pieceInput h 423 (by decide)
    have h426 : c426.eval a = true := atClause pieceInput h 425 (by decide)
    have h427 : c427.eval a = true := atClause pieceInput h 426 (by decide)
    have h429 : c429.eval a = true := atClause pieceInput h 428 (by decide)
    have h430 : c430.eval a = true := atClause pieceInput h 429 (by decide)
    have h432 : c432.eval a = true := atClause pieceInput h 431 (by decide)
    have h433 : c433.eval a = true := atClause pieceInput h 432 (by decide)
    have h435 : c435.eval a = true := atClause pieceInput h 434 (by decide)
    have h436 : c436.eval a = true := atClause pieceInput h 435 (by decide)
    have h438 : c438.eval a = true := atClause pieceInput h 437 (by decide)
    have h439 : c439.eval a = true := atClause pieceInput h 438 (by decide)
    have h441 : c441.eval a = true := atClause pieceInput h 440 (by decide)
    have h442 : c442.eval a = true := atClause pieceInput h 441 (by decide)
    have h444 : c444.eval a = true := atClause pieceInput h 443 (by decide)
    have h445 : c445.eval a = true := atClause pieceInput h 444 (by decide)
    have h446 : c446.eval a = true := atClause pieceInput h 445 (by decide)
    have h447 : c447.eval a = true := atClause pieceInput h 446 (by decide)
    have h449 : c449.eval a = true := atClause pieceInput h 448 (by decide)
    have h450 : c450.eval a = true := atClause pieceInput h 449 (by decide)
    have h452 : c452.eval a = true := atClause pieceInput h 451 (by decide)
    have h453 : c453.eval a = true := atClause pieceInput h 452 (by decide)
    have h455 : c455.eval a = true := atClause pieceInput h 454 (by decide)
    have h456 : c456.eval a = true := atClause pieceInput h 455 (by decide)
    have h458 : c458.eval a = true := atClause pieceInput h 457 (by decide)
    have h460 : c460.eval a = true := atClause pieceInput h 459 (by decide)
    have h461 : c461.eval a = true := atClause pieceInput h 460 (by decide)
    have h463 : c463.eval a = true := atClause pieceInput h 462 (by decide)
    have h464 : c464.eval a = true := atClause pieceInput h 463 (by decide)
    have h466 : c466.eval a = true := atClause pieceInput h 465 (by decide)
    have h467 : c467.eval a = true := atClause pieceInput h 466 (by decide)
    have h469 : c469.eval a = true := atClause pieceInput h 468 (by decide)
    have h470 : c470.eval a = true := atClause pieceInput h 469 (by decide)
    have h472 : c472.eval a = true := atClause pieceInput h 471 (by decide)
    have h473 : c473.eval a = true := atClause pieceInput h 472 (by decide)
    have h475 : c475.eval a = true := atClause pieceInput h 474 (by decide)
    have h476 : c476.eval a = true := atClause pieceInput h 475 (by decide)
    have h478 : c478.eval a = true := atClause pieceInput h 477 (by decide)
    have h479 : c479.eval a = true := atClause pieceInput h 478 (by decide)
    have h481 : c481.eval a = true := atClause pieceInput h 480 (by decide)
    have h482 : c482.eval a = true := atClause pieceInput h 481 (by decide)
    have h484 : c484.eval a = true := atClause pieceInput h 483 (by decide)
    have h485 : c485.eval a = true := atClause pieceInput h 484 (by decide)
    have h487 : c487.eval a = true := atClause pieceInput h 486 (by decide)
    have h488 : c488.eval a = true := atClause pieceInput h 487 (by decide)
    have h490 : c490.eval a = true := atClause pieceInput h 489 (by decide)
    have h491 : c491.eval a = true := atClause pieceInput h 490 (by decide)
    have h493 : c493.eval a = true := atClause pieceInput h 492 (by decide)
    have h494 : c494.eval a = true := atClause pieceInput h 493 (by decide)
    have h496 : c496.eval a = true := atClause pieceInput h 495 (by decide)
    have h497 : c497.eval a = true := atClause pieceInput h 496 (by decide)
    have h499 : c499.eval a = true := atClause pieceInput h 498 (by decide)
    have h500 : c500.eval a = true := atClause pieceInput h 499 (by decide)
    have h502 : c502.eval a = true := atClause pieceInput h 501 (by decide)
    have h503 : c503.eval a = true := atClause pieceInput h 502 (by decide)
    have h505 : c505.eval a = true := atClause pieceInput h 504 (by decide)
    have h506 : c506.eval a = true := atClause pieceInput h 505 (by decide)
    have h509 : c509.eval a = true := atClause pieceInput h 508 (by decide)
    have h513 : c513.eval a = true := atClause pieceInput h 512 (by decide)
    have h514 : c514.eval a = true := atClause pieceInput h 513 (by decide)
    have h516 : c516.eval a = true := atClause pieceInput h 515 (by decide)
    have h517 : c517.eval a = true := atClause pieceInput h 516 (by decide)
    have h519 : c519.eval a = true := atClause pieceInput h 518 (by decide)
    have h520 : c520.eval a = true := atClause pieceInput h 519 (by decide)
    have h522 : c522.eval a = true := atClause pieceInput h 521 (by decide)
    have h523 : c523.eval a = true := atClause pieceInput h 522 (by decide)
    have h525 : c525.eval a = true := atClause pieceInput h 524 (by decide)
    have h526 : c526.eval a = true := atClause pieceInput h 525 (by decide)
    have h527 : c527.eval a = true := atClause pieceInput h 526 (by decide)
    have h530 : c530.eval a = true := atClause pieceInput h 529 (by decide)
    have h533 : c533.eval a = true := atClause pieceInput h 532 (by decide)
    have h536 : c536.eval a = true := atClause pieceInput h 535 (by decide)
    have h539 : c539.eval a = true := atClause pieceInput h 538 (by decide)
    have h542 : c542.eval a = true := atClause pieceInput h 541 (by decide)
    have h546 : c546.eval a = true := atClause pieceInput h 545 (by decide)
    have h547 : c547.eval a = true := atClause pieceInput h 546 (by decide)
    have h549 : c549.eval a = true := atClause pieceInput h 548 (by decide)
    have h550 : c550.eval a = true := atClause pieceInput h 549 (by decide)
    have h552 : c552.eval a = true := atClause pieceInput h 551 (by decide)
    have h553 : c553.eval a = true := atClause pieceInput h 552 (by decide)
    have h555 : c555.eval a = true := atClause pieceInput h 554 (by decide)
    have h556 : c556.eval a = true := atClause pieceInput h 555 (by decide)
    have h558 : c558.eval a = true := atClause pieceInput h 557 (by decide)
    have h559 : c559.eval a = true := atClause pieceInput h 558 (by decide)
    have h560 : c560.eval a = true := atClause pieceInput h 559 (by decide)
    have h563 : c563.eval a = true := atClause pieceInput h 562 (by decide)
    have h566 : c566.eval a = true := atClause pieceInput h 565 (by decide)
    have h569 : c569.eval a = true := atClause pieceInput h 568 (by decide)
    have h572 : c572.eval a = true := atClause pieceInput h 571 (by decide)
    have h575 : c575.eval a = true := atClause pieceInput h 574 (by decide)
    have h579 : c579.eval a = true := atClause pieceInput h 578 (by decide)
    have h580 : c580.eval a = true := atClause pieceInput h 579 (by decide)
    have h582 : c582.eval a = true := atClause pieceInput h 581 (by decide)
    have h583 : c583.eval a = true := atClause pieceInput h 582 (by decide)
    have h585 : c585.eval a = true := atClause pieceInput h 584 (by decide)
    have h586 : c586.eval a = true := atClause pieceInput h 585 (by decide)
    have h588 : c588.eval a = true := atClause pieceInput h 587 (by decide)
    have h589 : c589.eval a = true := atClause pieceInput h 588 (by decide)
    have h591 : c591.eval a = true := atClause pieceInput h 590 (by decide)
    have h592 : c592.eval a = true := atClause pieceInput h 591 (by decide)
    have h594 : c594.eval a = true := atClause pieceInput h 593 (by decide)
    have h595 : c595.eval a = true := atClause pieceInput h 594 (by decide)
    have h596 : c596.eval a = true := atClause pieceInput h 595 (by decide)
    have h600 : c600.eval a = true := atClause pieceInput h 599 (by decide)
    have h601 : c601.eval a = true := atClause pieceInput h 600 (by decide)
    have h603 : c603.eval a = true := atClause pieceInput h 602 (by decide)
    have h604 : c604.eval a = true := atClause pieceInput h 603 (by decide)
    have h605 : c605.eval a = true := atClause pieceInput h 604 (by decide)
    have h609 : c609.eval a = true := atClause pieceInput h 608 (by decide)
    have h610 : c610.eval a = true := atClause pieceInput h 609 (by decide)
    have h612 : c612.eval a = true := atClause pieceInput h 611 (by decide)
    have h613 : c613.eval a = true := atClause pieceInput h 612 (by decide)
    have h614 : c614.eval a = true := atClause pieceInput h 613 (by decide)
    have h618 : c618.eval a = true := atClause pieceInput h 617 (by decide)
    have h621 : c621.eval a = true := atClause pieceInput h 620 (by decide)
    have h623 : c623.eval a = true := atClause pieceInput h 622 (by decide)
    have h625 : c625.eval a = true := atClause pieceInput h 624 (by decide)
    have h626 : c626.eval a = true := atClause pieceInput h 625 (by decide)
    have h628 : c628.eval a = true := atClause pieceInput h 627 (by decide)
    have h629 : c629.eval a = true := atClause pieceInput h 628 (by decide)
    have h631 : c631.eval a = true := atClause pieceInput h 630 (by decide)
    have h632 : c632.eval a = true := atClause pieceInput h 631 (by decide)
    have h634 : c634.eval a = true := atClause pieceInput h 633 (by decide)
    have h635 : c635.eval a = true := atClause pieceInput h 634 (by decide)
    have h637 : c637.eval a = true := atClause pieceInput h 636 (by decide)
    have h639 : c639.eval a = true := atClause pieceInput h 638 (by decide)
    have h642 : c642.eval a = true := atClause pieceInput h 641 (by decide)
    have h645 : c645.eval a = true := atClause pieceInput h 644 (by decide)
    have h648 : c648.eval a = true := atClause pieceInput h 647 (by decide)
    have h651 : c651.eval a = true := atClause pieceInput h 650 (by decide)
    have h654 : c654.eval a = true := atClause pieceInput h 653 (by decide)
    have h656 : c656.eval a = true := atClause pieceInput h 655 (by decide)
    have h658 : c658.eval a = true := atClause pieceInput h 657 (by decide)
    have h659 : c659.eval a = true := atClause pieceInput h 658 (by decide)
    have h661 : c661.eval a = true := atClause pieceInput h 660 (by decide)
    have h662 : c662.eval a = true := atClause pieceInput h 661 (by decide)
    have h664 : c664.eval a = true := atClause pieceInput h 663 (by decide)
    have h665 : c665.eval a = true := atClause pieceInput h 664 (by decide)
    have h667 : c667.eval a = true := atClause pieceInput h 666 (by decide)
    have h668 : c668.eval a = true := atClause pieceInput h 667 (by decide)
    have h670 : c670.eval a = true := atClause pieceInput h 669 (by decide)
    have h672 : c672.eval a = true := atClause pieceInput h 671 (by decide)
    have h675 : c675.eval a = true := atClause pieceInput h 674 (by decide)
    have h678 : c678.eval a = true := atClause pieceInput h 677 (by decide)
    have h681 : c681.eval a = true := atClause pieceInput h 680 (by decide)
    have h683 : c683.eval a = true := atClause pieceInput h 682 (by decide)
    have h684 : c684.eval a = true := atClause pieceInput h 683 (by decide)
    have h686 : c686.eval a = true := atClause pieceInput h 685 (by decide)
    have h687 : c687.eval a = true := atClause pieceInput h 686 (by decide)
    have h691 : c691.eval a = true := atClause pieceInput h 690 (by decide)
    have h693 : c693.eval a = true := atClause pieceInput h 692 (by decide)
    have h696 : c696.eval a = true := atClause pieceInput h 695 (by decide)
    have h698 : c698.eval a = true := atClause pieceInput h 697 (by decide)
    have h700 : c700.eval a = true := atClause pieceInput h 699 (by decide)
    have h701 : c701.eval a = true := atClause pieceInput h 700 (by decide)
    have h703 : c703.eval a = true := atClause pieceInput h 702 (by decide)
    have h704 : c704.eval a = true := atClause pieceInput h 703 (by decide)
    have h706 : c706.eval a = true := atClause pieceInput h 705 (by decide)
    have h707 : c707.eval a = true := atClause pieceInput h 706 (by decide)
    have h709 : c709.eval a = true := atClause pieceInput h 708 (by decide)
    have h710 : c710.eval a = true := atClause pieceInput h 709 (by decide)
    have h712 : c712.eval a = true := atClause pieceInput h 711 (by decide)
    have h713 : c713.eval a = true := atClause pieceInput h 712 (by decide)
    have h715 : c715.eval a = true := atClause pieceInput h 714 (by decide)
    have h717 : c717.eval a = true := atClause pieceInput h 716 (by decide)
    have h719 : c719.eval a = true := atClause pieceInput h 718 (by decide)
    have h721 : c721.eval a = true := atClause pieceInput h 720 (by decide)
    have h722 : c722.eval a = true := atClause pieceInput h 721 (by decide)
    have h724 : c724.eval a = true := atClause pieceInput h 723 (by decide)
    have h726 : c726.eval a = true := atClause pieceInput h 725 (by decide)
    have h728 : c728.eval a = true := atClause pieceInput h 727 (by decide)
    have h730 : c730.eval a = true := atClause pieceInput h 729 (by decide)
    have h731 : c731.eval a = true := atClause pieceInput h 730 (by decide)
    have h733 : c733.eval a = true := atClause pieceInput h 732 (by decide)
    have h735 : c735.eval a = true := atClause pieceInput h 734 (by decide)
    have h737 : c737.eval a = true := atClause pieceInput h 736 (by decide)
    have h738 : c738.eval a = true := atClause pieceInput h 737 (by decide)
    have h739 : c739.eval a = true := atClause pieceInput h 738 (by decide)
    have h740 := step740 a h738 h360 h505 h85 h667 h229 h500
    have h741 := step741 a h738 h357 h497 h81 h662 h225 h496
    have h742 := step742 a h738 h357 h499 h664 h81 h225 h494
    have h743 := step743 a h738 h360 h651 h654 h742 h741 h740 h265 h696 h269 h503 h665 h85 h229 h502
    have h744 := step744 a h739 h388 h450 h49 h684 h241 h446
    have h745 := step745 a h739 h388 h449 h683 h49 h241 h447
    have h746 := step746 a h739 h391 h455 h53 h686 h245 h453
    have h747 := step747 a h739 h391 h406 h409 h744 h745 h746 h249 h691 h253 h456 h687 h53 h245 h452
    have h748 := step748 a h469 h61 h703 h277 h464
    have h749 := step749 a h461 h57 h698 h273 h460
    have h750 := step750 a h467 h701 h61 h277 h466
    have h751 := step751 a h672 h675 h411 h414 h749 h748 h750 h293 h717 h289 h463 h700 h57 h273 h458
    have h752 := step752 a h517 h89 h526 h101 h513
    have h753 := step753 a h752 h105 h516 h525 h89 h101 h514
    have h754 := step754 a h737 h335 h373 h13 h523 h97 h369
    have h755 := step755 a h737 h332 h366 h9 h519 h93 h364
    have h756 := step756 a h737 h335 h372 h522 h13 h97 h370
    have h757 := step757 a h737 h332 h506 h509 h755 h756 h754 h133 h572 h129 h367 h520 h9 h93 h363
    have h758 := step758 a h445 h45 h604 h173 h441
    have h759 := step759 a h438 h41 h600 h169 h436
    have h760 := step760 a h444 h603 h45 h173 h442
    have h761 := step761 a h533 h536 h398 h401 h759 h758 h760 h181 h605 h177 h439 h601 h41 h169 h435
    have h762 := step762 a h549 h109 h558 h121 h547
    have h763 := step763 a h762 h125 h550 h559 h109 h121 h546
    have h764 := step764 a h737 h341 h385 h21 h556 h117 h381
    have h765 := step765 a h737 h338 h378 h17 h552 h113 h376
    have h766 := step766 a h737 h341 h384 h555 h21 h117 h382
    have h767 := step767 a h737 h338 h539 h542 h765 h766 h764 h141 h575 h137 h379 h553 h17 h113 h375
    have h768 := step768 a h433 h37 h583 h149 h429
    have h769 := step769 a h426 h33 h579 h145 h424
    have h770 := step770 a h432 h582 h37 h149 h430
    have h771 := step771 a h560 h563 h392 h395 h769 h768 h770 h165 h596 h161 h427 h580 h33 h145 h423
    have h772 := step772 a h757 h767 h761 h771 h753 h763 h530 h569 h595 h157 h613 h189 h591
    have h773 := step773 a h757 h767 h761 h771 h753 h763 h527 h566 h588 h153 h609 h185 h586
    have h774 := step774 a h757 h767 h761 h771 h753 h763 h594 h612 h530 h569 h157 h189 h592
    have h775 := step775 a h757 h767 h761 h771 h772 h773 h774 h753 h763 h197 h527 h566 h614 h193 h589 h610 h153 h185 h585
    have h776 := step776 a h743 h656 h221 h668 h237 h661
    have h777 := step777 a h743 h747 h775 h29 h751 h776 h233 h658 h670 h221 h237 h659
    have h778 := step778 a h738 h354 h493 h77 h634 h209 h488
    have h779 := step779 a h738 h351 h485 h73 h629 h205 h484
    have h780 := step780 a h738 h351 h487 h631 h73 h205 h482
    have h781 := step781 a h738 h354 h618 h621 h780 h779 h778 h257 h693 h261 h491 h632 h77 h209 h490
    have h782 := step782 a h747 h775 h29 h420 h481 h69 h724 h301 h476
    have h783 := step783 a h747 h775 h29 h417 h473 h65 h719 h297 h472
    have h784 := step784 a h747 h775 h29 h417 h475 h721 h65 h297 h470
    have h785 := step785 a h747 h775 h29 h420 h645 h648 h784 h783 h782 h305 h726 h309 h479 h722 h69 h301 h478
    have h786 := step786 a h781 h628 h201 h637 h213 h623
    have h787 := step787 a h781 h785 h786 h217 h626 h635 h201 h213 h625
    have h788 := step788 a h777 h681 h787 h642 h715 h285 h733 h317 h710
    have h789 := step789 a h777 h681 h787 h642 h713 h731 h285 h317 h712
    have h790 := step790 a h777 h678 h787 h639 h707 h281 h728 h313 h706
    have h791 := step791 a h777 h678 h787 h639 h788 h789 h325 h735 h790 h321 h709 h730 h281 h313 h704
    exact Bool.noConfusion h791
#print axioms pieces_unsat
theorem bound_to_fixture : PublishedInput.cnf.Unsat := pieces_unsat
/-- info: 'bound_to_fixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bound_to_fixture

import LocalRup.Core

namespace LocalRup.SymmetryFree

set_option maxRecDepth 100000
set_option maxHeartbeats 0
def variables : Nat := 246
def comments : List String := []
def inputBlock0 : Formula := [
  [(0, true), (1, true), (2, true)],
  [(0, false), (1, false)],
  [(0, false), (2, false)],
  [(1, false), (2, false)],
  [(3, true), (4, true), (5, true)],
  [(3, false), (4, false)],
  [(3, false), (5, false)],
  [(4, false), (5, false)],
  [(6, true), (7, true), (8, true)],
  [(6, false), (7, false)],
  [(6, false), (8, false)],
  [(7, false), (8, false)],
  [(9, true), (10, true), (11, true)],
  [(9, false), (10, false)],
  [(9, false), (11, false)],
  [(10, false), (11, false)]]
def inputBlock1 : Formula := [
  [(12, true), (13, true), (14, true)],
  [(12, false), (13, false)],
  [(12, false), (14, false)],
  [(13, false), (14, false)],
  [(15, true), (16, true), (17, true)],
  [(15, false), (16, false)],
  [(15, false), (17, false)],
  [(16, false), (17, false)],
  [(18, true), (19, true), (20, true)],
  [(18, false), (19, false)],
  [(18, false), (20, false)],
  [(19, false), (20, false)],
  [(21, true), (22, true), (23, true)],
  [(21, false), (22, false)],
  [(21, false), (23, false)],
  [(22, false), (23, false)]]
def inputBlock2 : Formula := [
  [(24, true), (25, true), (26, true)],
  [(24, false), (25, false)],
  [(24, false), (26, false)],
  [(25, false), (26, false)],
  [(27, true), (28, true), (29, true)],
  [(27, false), (28, false)],
  [(27, false), (29, false)],
  [(28, false), (29, false)],
  [(30, true), (31, true), (32, true)],
  [(30, false), (31, false)],
  [(30, false), (32, false)],
  [(31, false), (32, false)],
  [(33, true), (34, true), (35, true)],
  [(33, false), (34, false)],
  [(33, false), (35, false)],
  [(34, false), (35, false)]]
def inputBlock3 : Formula := [
  [(36, true), (37, true), (38, true)],
  [(36, false), (37, false)],
  [(36, false), (38, false)],
  [(37, false), (38, false)],
  [(39, true), (40, true), (41, true)],
  [(39, false), (40, false)],
  [(39, false), (41, false)],
  [(40, false), (41, false)],
  [(42, true), (43, true), (44, true)],
  [(42, false), (43, false)],
  [(42, false), (44, false)],
  [(43, false), (44, false)],
  [(45, true), (46, true), (47, true)],
  [(45, false), (46, false)],
  [(45, false), (47, false)],
  [(46, false), (47, false)]]
def inputBlock4 : Formula := [
  [(48, true), (49, true), (50, true)],
  [(48, false), (49, false)],
  [(48, false), (50, false)],
  [(49, false), (50, false)],
  [(51, true), (52, true), (53, true)],
  [(51, false), (52, false)],
  [(51, false), (53, false)],
  [(52, false), (53, false)],
  [(54, true), (55, true), (56, true)],
  [(54, false), (55, false)],
  [(54, false), (56, false)],
  [(55, false), (56, false)],
  [(57, true), (58, true), (59, true)],
  [(57, false), (58, false)],
  [(57, false), (59, false)],
  [(58, false), (59, false)]]
def inputBlock5 : Formula := [
  [(60, true), (61, true), (62, true)],
  [(60, false), (61, false)],
  [(60, false), (62, false)],
  [(61, false), (62, false)],
  [(63, true), (64, true), (65, true)],
  [(63, false), (64, false)],
  [(63, false), (65, false)],
  [(64, false), (65, false)],
  [(66, true), (67, true), (68, true)],
  [(66, false), (67, false)],
  [(66, false), (68, false)],
  [(67, false), (68, false)],
  [(69, true), (70, true), (71, true)],
  [(69, false), (70, false)],
  [(69, false), (71, false)],
  [(70, false), (71, false)]]
def inputBlock6 : Formula := [
  [(72, true), (73, true), (74, true)],
  [(72, false), (73, false)],
  [(72, false), (74, false)],
  [(73, false), (74, false)],
  [(75, true), (76, true), (77, true)],
  [(75, false), (76, false)],
  [(75, false), (77, false)],
  [(76, false), (77, false)],
  [(78, true), (79, true), (80, true)],
  [(78, false), (79, false)],
  [(78, false), (80, false)],
  [(79, false), (80, false)],
  [(81, true), (82, true), (83, true)],
  [(81, false), (82, false)],
  [(81, false), (83, false)],
  [(82, false), (83, false)]]
def inputBlock7 : Formula := [
  [(84, true), (85, true), (86, true)],
  [(84, false), (85, false)],
  [(84, false), (86, false)],
  [(85, false), (86, false)],
  [(87, true), (88, true), (89, true)],
  [(87, false), (88, false)],
  [(87, false), (89, false)],
  [(88, false), (89, false)],
  [(90, true), (91, true), (92, true)],
  [(90, false), (91, false)],
  [(90, false), (92, false)],
  [(91, false), (92, false)],
  [(93, true), (94, true), (95, true)],
  [(93, false), (94, false)],
  [(93, false), (95, false)],
  [(94, false), (95, false)]]
def inputBlock8 : Formula := [
  [(96, true), (97, true), (98, true)],
  [(96, false), (97, false)],
  [(96, false), (98, false)],
  [(97, false), (98, false)],
  [(99, true), (100, true), (101, true)],
  [(99, false), (100, false)],
  [(99, false), (101, false)],
  [(100, false), (101, false)],
  [(102, true), (103, true), (104, true)],
  [(102, false), (103, false)],
  [(102, false), (104, false)],
  [(103, false), (104, false)],
  [(105, true), (106, true), (107, true)],
  [(105, false), (106, false)],
  [(105, false), (107, false)],
  [(106, false), (107, false)]]
def inputBlock9 : Formula := [
  [(108, true), (109, true), (110, true)],
  [(108, false), (109, false)],
  [(108, false), (110, false)],
  [(109, false), (110, false)],
  [(111, true), (112, true), (113, true)],
  [(111, false), (112, false)],
  [(111, false), (113, false)],
  [(112, false), (113, false)],
  [(114, true), (115, true), (116, true)],
  [(114, false), (115, false)],
  [(114, false), (116, false)],
  [(115, false), (116, false)],
  [(117, true), (118, true), (119, true)],
  [(117, false), (118, false)],
  [(117, false), (119, false)],
  [(118, false), (119, false)]]
def inputBlock10 : Formula := [
  [(120, true), (121, true), (122, true)],
  [(120, false), (121, false)],
  [(120, false), (122, false)],
  [(121, false), (122, false)],
  [(123, true), (124, true), (125, true)],
  [(123, false), (124, false)],
  [(123, false), (125, false)],
  [(124, false), (125, false)],
  [(126, true), (127, true), (128, true)],
  [(126, false), (127, false)],
  [(126, false), (128, false)],
  [(127, false), (128, false)],
  [(129, true), (130, true), (131, true)],
  [(129, false), (130, false)],
  [(129, false), (131, false)],
  [(130, false), (131, false)]]
def inputBlock11 : Formula := [
  [(132, true), (133, true), (134, true)],
  [(132, false), (133, false)],
  [(132, false), (134, false)],
  [(133, false), (134, false)],
  [(135, true), (136, true), (137, true)],
  [(135, false), (136, false)],
  [(135, false), (137, false)],
  [(136, false), (137, false)],
  [(138, true), (139, true), (140, true)],
  [(138, false), (139, false)],
  [(138, false), (140, false)],
  [(139, false), (140, false)],
  [(141, true), (142, true), (143, true)],
  [(141, false), (142, false)],
  [(141, false), (143, false)],
  [(142, false), (143, false)]]
def inputBlock12 : Formula := [
  [(144, true), (145, true), (146, true)],
  [(144, false), (145, false)],
  [(144, false), (146, false)],
  [(145, false), (146, false)],
  [(147, true), (148, true), (149, true)],
  [(147, false), (148, false)],
  [(147, false), (149, false)],
  [(148, false), (149, false)],
  [(150, true), (151, true), (152, true)],
  [(150, false), (151, false)],
  [(150, false), (152, false)],
  [(151, false), (152, false)],
  [(153, true), (154, true), (155, true)],
  [(153, false), (154, false)],
  [(153, false), (155, false)],
  [(154, false), (155, false)]]
def inputBlock13 : Formula := [
  [(156, true), (157, true), (158, true)],
  [(156, false), (157, false)],
  [(156, false), (158, false)],
  [(157, false), (158, false)],
  [(159, true), (160, true), (161, true)],
  [(159, false), (160, false)],
  [(159, false), (161, false)],
  [(160, false), (161, false)],
  [(162, true), (163, true), (164, true)],
  [(162, false), (163, false)],
  [(162, false), (164, false)],
  [(163, false), (164, false)],
  [(165, true), (166, true), (167, true)],
  [(165, false), (166, false)],
  [(165, false), (167, false)],
  [(166, false), (167, false)]]
def inputBlock14 : Formula := [
  [(168, true), (169, true), (170, true)],
  [(168, false), (169, false)],
  [(168, false), (170, false)],
  [(169, false), (170, false)],
  [(171, true), (172, true), (173, true)],
  [(171, false), (172, false)],
  [(171, false), (173, false)],
  [(172, false), (173, false)],
  [(174, true), (175, true), (176, true)],
  [(174, false), (175, false)],
  [(174, false), (176, false)],
  [(175, false), (176, false)],
  [(177, true), (178, true), (179, true)],
  [(177, false), (178, false)],
  [(177, false), (179, false)],
  [(178, false), (179, false)]]
def inputBlock15 : Formula := [
  [(180, true), (181, true), (182, true)],
  [(180, false), (181, false)],
  [(180, false), (182, false)],
  [(181, false), (182, false)],
  [(183, true), (184, true), (185, true)],
  [(183, false), (184, false)],
  [(183, false), (185, false)],
  [(184, false), (185, false)],
  [(186, true), (187, true), (188, true)],
  [(186, false), (187, false)],
  [(186, false), (188, false)],
  [(187, false), (188, false)],
  [(189, true), (190, true), (191, true)],
  [(189, false), (190, false)],
  [(189, false), (191, false)],
  [(190, false), (191, false)]]
def inputBlock16 : Formula := [
  [(192, true), (193, true), (194, true)],
  [(192, false), (193, false)],
  [(192, false), (194, false)],
  [(193, false), (194, false)],
  [(195, true), (196, true), (197, true)],
  [(195, false), (196, false)],
  [(195, false), (197, false)],
  [(196, false), (197, false)],
  [(198, true), (199, true), (200, true)],
  [(198, false), (199, false)],
  [(198, false), (200, false)],
  [(199, false), (200, false)],
  [(201, true), (202, true), (203, true)],
  [(201, false), (202, false)],
  [(201, false), (203, false)],
  [(202, false), (203, false)]]
def inputBlock17 : Formula := [
  [(204, true), (205, true), (206, true)],
  [(204, false), (205, false)],
  [(204, false), (206, false)],
  [(205, false), (206, false)],
  [(207, true), (208, true), (209, true)],
  [(207, false), (208, false)],
  [(207, false), (209, false)],
  [(208, false), (209, false)],
  [(210, true), (211, true), (212, true)],
  [(210, false), (211, false)],
  [(210, false), (212, false)],
  [(211, false), (212, false)],
  [(213, true), (214, true), (215, true)],
  [(213, false), (214, false)],
  [(213, false), (215, false)],
  [(214, false), (215, false)]]
def inputBlock18 : Formula := [
  [(216, true), (217, true), (218, true)],
  [(216, false), (217, false)],
  [(216, false), (218, false)],
  [(217, false), (218, false)],
  [(219, true), (220, true), (221, true)],
  [(219, false), (220, false)],
  [(219, false), (221, false)],
  [(220, false), (221, false)],
  [(222, true), (223, true), (224, true)],
  [(222, false), (223, false)],
  [(222, false), (224, false)],
  [(223, false), (224, false)],
  [(225, true), (226, true), (227, true)],
  [(225, false), (226, false)],
  [(225, false), (227, false)],
  [(226, false), (227, false)]]
def inputBlock19 : Formula := [
  [(228, true), (229, true), (230, true)],
  [(228, false), (229, false)],
  [(228, false), (230, false)],
  [(229, false), (230, false)],
  [(231, true), (232, true), (233, true)],
  [(231, false), (232, false)],
  [(231, false), (233, false)],
  [(232, false), (233, false)],
  [(234, true), (235, true), (236, true)],
  [(234, false), (235, false)],
  [(234, false), (236, false)],
  [(235, false), (236, false)],
  [(237, true), (238, true), (239, true)],
  [(237, false), (238, false)],
  [(237, false), (239, false)],
  [(238, false), (239, false)]]
def inputBlock20 : Formula := [
  [(240, true), (241, true), (242, true)],
  [(240, false), (241, false)],
  [(240, false), (242, false)],
  [(241, false), (242, false)],
  [(243, true), (244, true), (245, true)],
  [(243, false), (244, false)],
  [(243, false), (245, false)],
  [(244, false), (245, false)],
  [(0, false), (3, false)],
  [(1, false), (4, false)],
  [(2, false), (5, false)],
  [(0, false), (6, false)],
  [(1, false), (7, false)],
  [(2, false), (8, false)],
  [(0, false), (9, false)],
  [(1, false), (10, false)]]
def inputBlock21 : Formula := [
  [(2, false), (11, false)],
  [(0, false), (12, false)],
  [(1, false), (13, false)],
  [(2, false), (14, false)],
  [(0, false), (15, false)],
  [(1, false), (16, false)],
  [(2, false), (17, false)],
  [(0, false), (18, false)],
  [(1, false), (19, false)],
  [(2, false), (20, false)],
  [(3, false), (18, false)],
  [(4, false), (19, false)],
  [(5, false), (20, false)],
  [(3, false), (54, false)],
  [(4, false), (55, false)],
  [(5, false), (56, false)]]
def inputBlock22 : Formula := [
  [(3, false), (57, false)],
  [(4, false), (58, false)],
  [(5, false), (59, false)],
  [(3, false), (60, false)],
  [(4, false), (61, false)],
  [(5, false), (62, false)],
  [(3, false), (63, false)],
  [(4, false), (64, false)],
  [(5, false), (65, false)],
  [(6, false), (69, false)],
  [(7, false), (70, false)],
  [(8, false), (71, false)],
  [(6, false), (96, false)],
  [(7, false), (97, false)],
  [(8, false), (98, false)],
  [(9, false), (72, false)]]
def inputBlock23 : Formula := [
  [(10, false), (73, false)],
  [(11, false), (74, false)],
  [(9, false), (99, false)],
  [(10, false), (100, false)],
  [(11, false), (101, false)],
  [(12, false), (84, false)],
  [(13, false), (85, false)],
  [(14, false), (86, false)],
  [(12, false), (102, false)],
  [(13, false), (103, false)],
  [(14, false), (104, false)],
  [(15, false), (87, false)],
  [(16, false), (88, false)],
  [(17, false), (89, false)],
  [(15, false), (105, false)],
  [(16, false), (106, false)]]
def inputBlock24 : Formula := [
  [(17, false), (107, false)],
  [(18, false), (180, false)],
  [(19, false), (181, false)],
  [(20, false), (182, false)],
  [(18, false), (183, false)],
  [(19, false), (184, false)],
  [(20, false), (185, false)],
  [(21, false), (24, false)],
  [(22, false), (25, false)],
  [(23, false), (26, false)],
  [(21, false), (27, false)],
  [(22, false), (28, false)],
  [(23, false), (29, false)],
  [(21, false), (30, false)],
  [(22, false), (31, false)],
  [(23, false), (32, false)]]
def inputBlock25 : Formula := [
  [(21, false), (33, false)],
  [(22, false), (34, false)],
  [(23, false), (35, false)],
  [(21, false), (36, false)],
  [(22, false), (37, false)],
  [(23, false), (38, false)],
  [(21, false), (39, false)],
  [(22, false), (40, false)],
  [(23, false), (41, false)],
  [(21, false), (42, false)],
  [(22, false), (43, false)],
  [(23, false), (44, false)],
  [(21, false), (45, false)],
  [(22, false), (46, false)],
  [(23, false), (47, false)],
  [(21, false), (48, false)]]
def inputBlock26 : Formula := [
  [(22, false), (49, false)],
  [(23, false), (50, false)],
  [(21, false), (51, false)],
  [(22, false), (52, false)],
  [(23, false), (53, false)],
  [(24, false), (108, false)],
  [(25, false), (109, false)],
  [(26, false), (110, false)],
  [(24, false), (120, false)],
  [(25, false), (121, false)],
  [(26, false), (122, false)],
  [(27, false), (111, false)],
  [(28, false), (112, false)],
  [(29, false), (113, false)],
  [(27, false), (123, false)],
  [(28, false), (124, false)]]
def inputBlock27 : Formula := [
  [(29, false), (125, false)],
  [(30, false), (126, false)],
  [(31, false), (127, false)],
  [(32, false), (128, false)],
  [(30, false), (132, false)],
  [(31, false), (133, false)],
  [(32, false), (134, false)],
  [(33, false), (129, false)],
  [(34, false), (130, false)],
  [(35, false), (131, false)],
  [(33, false), (135, false)],
  [(34, false), (136, false)],
  [(35, false), (137, false)],
  [(36, false), (180, false)],
  [(37, false), (181, false)],
  [(38, false), (182, false)]]
def inputBlock28 : Formula := [
  [(36, false), (186, false)],
  [(37, false), (187, false)],
  [(38, false), (188, false)],
  [(39, false), (183, false)],
  [(40, false), (184, false)],
  [(41, false), (185, false)],
  [(39, false), (189, false)],
  [(40, false), (190, false)],
  [(41, false), (191, false)],
  [(42, false), (204, false)],
  [(43, false), (205, false)],
  [(44, false), (206, false)],
  [(42, false), (216, false)],
  [(43, false), (217, false)],
  [(44, false), (218, false)],
  [(45, false), (207, false)]]
def inputBlock29 : Formula := [
  [(46, false), (208, false)],
  [(47, false), (209, false)],
  [(45, false), (219, false)],
  [(46, false), (220, false)],
  [(47, false), (221, false)],
  [(48, false), (222, false)],
  [(49, false), (223, false)],
  [(50, false), (224, false)],
  [(48, false), (228, false)],
  [(49, false), (229, false)],
  [(50, false), (230, false)],
  [(51, false), (225, false)],
  [(52, false), (226, false)],
  [(53, false), (227, false)],
  [(51, false), (231, false)],
  [(52, false), (232, false)]]
def inputBlock30 : Formula := [
  [(53, false), (233, false)],
  [(54, false), (153, false)],
  [(55, false), (154, false)],
  [(56, false), (155, false)],
  [(54, false), (192, false)],
  [(55, false), (193, false)],
  [(56, false), (194, false)],
  [(57, false), (156, false)],
  [(58, false), (157, false)],
  [(59, false), (158, false)],
  [(57, false), (195, false)],
  [(58, false), (196, false)],
  [(59, false), (197, false)],
  [(60, false), (168, false)],
  [(61, false), (169, false)],
  [(62, false), (170, false)]]
def inputBlock31 : Formula := [
  [(60, false), (198, false)],
  [(61, false), (199, false)],
  [(62, false), (200, false)],
  [(63, false), (171, false)],
  [(64, false), (172, false)],
  [(65, false), (173, false)],
  [(63, false), (201, false)],
  [(64, false), (202, false)],
  [(65, false), (203, false)],
  [(66, false), (69, false)],
  [(67, false), (70, false)],
  [(68, false), (71, false)],
  [(66, false), (72, false)],
  [(67, false), (73, false)],
  [(68, false), (74, false)],
  [(66, false), (75, false)]]
def inputBlock32 : Formula := [
  [(67, false), (76, false)],
  [(68, false), (77, false)],
  [(66, false), (78, false)],
  [(67, false), (79, false)],
  [(68, false), (80, false)],
  [(69, false), (96, false)],
  [(70, false), (97, false)],
  [(71, false), (98, false)],
  [(72, false), (99, false)],
  [(73, false), (100, false)],
  [(74, false), (101, false)],
  [(75, false), (78, false)],
  [(76, false), (79, false)],
  [(77, false), (80, false)],
  [(75, false), (114, false)],
  [(76, false), (115, false)]]
def inputBlock33 : Formula := [
  [(77, false), (116, false)],
  [(75, false), (117, false)],
  [(76, false), (118, false)],
  [(77, false), (119, false)],
  [(78, false), (126, false)],
  [(79, false), (127, false)],
  [(80, false), (128, false)],
  [(78, false), (129, false)],
  [(79, false), (130, false)],
  [(80, false), (131, false)],
  [(81, false), (84, false)],
  [(82, false), (85, false)],
  [(83, false), (86, false)],
  [(81, false), (87, false)],
  [(82, false), (88, false)],
  [(83, false), (89, false)]]
def inputBlock34 : Formula := [
  [(81, false), (90, false)],
  [(82, false), (91, false)],
  [(83, false), (92, false)],
  [(81, false), (93, false)],
  [(82, false), (94, false)],
  [(83, false), (95, false)],
  [(84, false), (102, false)],
  [(85, false), (103, false)],
  [(86, false), (104, false)],
  [(87, false), (105, false)],
  [(88, false), (106, false)],
  [(89, false), (107, false)],
  [(90, false), (93, false)],
  [(91, false), (94, false)],
  [(92, false), (95, false)],
  [(90, false), (108, false)]]
def inputBlock35 : Formula := [
  [(91, false), (109, false)],
  [(92, false), (110, false)],
  [(90, false), (111, false)],
  [(91, false), (112, false)],
  [(92, false), (113, false)],
  [(93, false), (138, false)],
  [(94, false), (139, false)],
  [(95, false), (140, false)],
  [(93, false), (141, false)],
  [(94, false), (142, false)],
  [(95, false), (143, false)],
  [(96, false), (99, false)],
  [(97, false), (100, false)],
  [(98, false), (101, false)],
  [(102, false), (105, false)],
  [(103, false), (106, false)]]
def inputBlock36 : Formula := [
  [(104, false), (107, false)],
  [(108, false), (120, false)],
  [(109, false), (121, false)],
  [(110, false), (122, false)],
  [(111, false), (123, false)],
  [(112, false), (124, false)],
  [(113, false), (125, false)],
  [(114, false), (138, false)],
  [(115, false), (139, false)],
  [(116, false), (140, false)],
  [(114, false), (144, false)],
  [(115, false), (145, false)],
  [(116, false), (146, false)],
  [(117, false), (141, false)],
  [(118, false), (142, false)],
  [(119, false), (143, false)]]
def inputBlock37 : Formula := [
  [(117, false), (147, false)],
  [(118, false), (148, false)],
  [(119, false), (149, false)],
  [(120, false), (123, false)],
  [(121, false), (124, false)],
  [(122, false), (125, false)],
  [(126, false), (132, false)],
  [(127, false), (133, false)],
  [(128, false), (134, false)],
  [(129, false), (135, false)],
  [(130, false), (136, false)],
  [(131, false), (137, false)],
  [(132, false), (135, false)],
  [(133, false), (136, false)],
  [(134, false), (137, false)],
  [(138, false), (144, false)]]
def inputBlock38 : Formula := [
  [(139, false), (145, false)],
  [(140, false), (146, false)],
  [(141, false), (147, false)],
  [(142, false), (148, false)],
  [(143, false), (149, false)],
  [(144, false), (147, false)],
  [(145, false), (148, false)],
  [(146, false), (149, false)],
  [(150, false), (153, false)],
  [(151, false), (154, false)],
  [(152, false), (155, false)],
  [(150, false), (156, false)],
  [(151, false), (157, false)],
  [(152, false), (158, false)],
  [(150, false), (159, false)],
  [(151, false), (160, false)]]
def inputBlock39 : Formula := [
  [(152, false), (161, false)],
  [(150, false), (162, false)],
  [(151, false), (163, false)],
  [(152, false), (164, false)],
  [(153, false), (192, false)],
  [(154, false), (193, false)],
  [(155, false), (194, false)],
  [(156, false), (195, false)],
  [(157, false), (196, false)],
  [(158, false), (197, false)],
  [(159, false), (162, false)],
  [(160, false), (163, false)],
  [(161, false), (164, false)],
  [(159, false), (210, false)],
  [(160, false), (211, false)],
  [(161, false), (212, false)]]
def inputBlock40 : Formula := [
  [(159, false), (213, false)],
  [(160, false), (214, false)],
  [(161, false), (215, false)],
  [(162, false), (222, false)],
  [(163, false), (223, false)],
  [(164, false), (224, false)],
  [(162, false), (225, false)],
  [(163, false), (226, false)],
  [(164, false), (227, false)],
  [(165, false), (168, false)],
  [(166, false), (169, false)],
  [(167, false), (170, false)],
  [(165, false), (171, false)],
  [(166, false), (172, false)],
  [(167, false), (173, false)],
  [(165, false), (174, false)]]
def inputBlock41 : Formula := [
  [(166, false), (175, false)],
  [(167, false), (176, false)],
  [(165, false), (177, false)],
  [(166, false), (178, false)],
  [(167, false), (179, false)],
  [(168, false), (198, false)],
  [(169, false), (199, false)],
  [(170, false), (200, false)],
  [(171, false), (201, false)],
  [(172, false), (202, false)],
  [(173, false), (203, false)],
  [(174, false), (177, false)],
  [(175, false), (178, false)],
  [(176, false), (179, false)],
  [(174, false), (204, false)],
  [(175, false), (205, false)]]
def inputBlock42 : Formula := [
  [(176, false), (206, false)],
  [(174, false), (207, false)],
  [(175, false), (208, false)],
  [(176, false), (209, false)],
  [(177, false), (234, false)],
  [(178, false), (235, false)],
  [(179, false), (236, false)],
  [(177, false), (237, false)],
  [(178, false), (238, false)],
  [(179, false), (239, false)],
  [(180, false), (186, false)],
  [(181, false), (187, false)],
  [(182, false), (188, false)],
  [(183, false), (189, false)],
  [(184, false), (190, false)],
  [(185, false), (191, false)]]
def inputBlock43 : Formula := [
  [(186, false), (189, false)],
  [(187, false), (190, false)],
  [(188, false), (191, false)],
  [(192, false), (195, false)],
  [(193, false), (196, false)],
  [(194, false), (197, false)],
  [(198, false), (201, false)],
  [(199, false), (202, false)],
  [(200, false), (203, false)],
  [(204, false), (216, false)],
  [(205, false), (217, false)],
  [(206, false), (218, false)],
  [(207, false), (219, false)],
  [(208, false), (220, false)],
  [(209, false), (221, false)],
  [(210, false), (234, false)]]
def inputBlock44 : Formula := [
  [(211, false), (235, false)],
  [(212, false), (236, false)],
  [(210, false), (240, false)],
  [(211, false), (241, false)],
  [(212, false), (242, false)],
  [(213, false), (237, false)],
  [(214, false), (238, false)],
  [(215, false), (239, false)],
  [(213, false), (243, false)],
  [(214, false), (244, false)],
  [(215, false), (245, false)],
  [(216, false), (219, false)],
  [(217, false), (220, false)],
  [(218, false), (221, false)],
  [(222, false), (228, false)],
  [(223, false), (229, false)]]
def inputBlock45 : Formula := [
  [(224, false), (230, false)],
  [(225, false), (231, false)],
  [(226, false), (232, false)],
  [(227, false), (233, false)],
  [(228, false), (231, false)],
  [(229, false), (232, false)],
  [(230, false), (233, false)],
  [(234, false), (240, false)],
  [(235, false), (241, false)],
  [(236, false), (242, false)],
  [(237, false), (243, false)],
  [(238, false), (244, false)],
  [(239, false), (245, false)],
  [(240, false), (243, false)],
  [(241, false), (244, false)],
  [(242, false), (245, false)]]
def input : Formula := (((((inputBlock0 ++ inputBlock1) ++ (inputBlock2 ++ (inputBlock3 ++ inputBlock4))) ++ ((inputBlock5 ++ (inputBlock6 ++ inputBlock7)) ++ (inputBlock8 ++ (inputBlock9 ++ inputBlock10)))) ++ (((inputBlock11 ++ (inputBlock12 ++ inputBlock13)) ++ (inputBlock14 ++ (inputBlock15 ++ inputBlock16))) ++ ((inputBlock17 ++ (inputBlock18 ++ inputBlock19)) ++ (inputBlock20 ++ (inputBlock21 ++ inputBlock22))))) ++ ((((inputBlock23 ++ inputBlock24) ++ (inputBlock25 ++ (inputBlock26 ++ inputBlock27))) ++ ((inputBlock28 ++ (inputBlock29 ++ inputBlock30)) ++ (inputBlock31 ++ (inputBlock32 ++ inputBlock33)))) ++ (((inputBlock34 ++ (inputBlock35 ++ inputBlock36)) ++ (inputBlock37 ++ (inputBlock38 ++ inputBlock39))) ++ ((inputBlock40 ++ (inputBlock41 ++ inputBlock42)) ++ (inputBlock43 ++ (inputBlock44 ++ inputBlock45))))))

def cnf : Std.Sat.CNF Nat := ⟨input.toArray⟩

def state0 : Known := initial input
def hint0Block0 : List Nat := [2, 3, 4, 6, 7, 10, 11, 12, 14, 15]
def hint0Block1 : List Nat := [16, 18, 19, 20, 22, 23, 24, 26, 27, 28]
def hint0Block2 : List Nat := [30, 31, 32, 34, 35, 36, 38, 39, 40, 42]
def hint0Block3 : List Nat := [43, 44, 46, 47, 48, 50, 51, 52, 54, 55]
def hint0Block4 : List Nat := [56, 58, 59, 60, 62, 63, 64, 66, 67, 68]
def hint0Block5 : List Nat := [70, 71, 72, 74, 75, 76, 78, 79, 80, 82]
def hint0Block6 : List Nat := [83, 84, 86, 87, 88, 90, 91, 92, 94, 95]
def hint0Block7 : List Nat := [96, 98, 99, 100, 102, 103, 104, 106, 107, 108]
def hint0Block8 : List Nat := [110, 111, 112, 114, 115, 116, 118, 119, 120, 122]
def hint0Block9 : List Nat := [123, 124, 127, 128, 130, 131, 132, 134, 135, 136]
def hint0Block10 : List Nat := [138, 139, 140, 142, 143, 144, 146, 147, 148, 150]
def hint0Block11 : List Nat := [151, 152, 154, 155, 156, 158, 159, 160, 162, 163]
def hint0Block12 : List Nat := [164, 166, 167, 168, 170, 171, 172, 174, 175, 176]
def hint0Block13 : List Nat := [178, 179, 180, 182, 183, 184, 186, 187, 188, 190]
def hint0Block14 : List Nat := [191, 192, 194, 195, 196, 198, 199, 200, 202, 203]
def hint0Block15 : List Nat := [204, 206, 207, 208, 210, 211, 212, 214, 215, 218]
def hint0Block16 : List Nat := [219, 220, 222, 223, 224, 226, 227, 228, 230, 231]
def hint0Block17 : List Nat := [232, 234, 235, 236, 238, 239, 240, 242, 243, 244]
def hint0Block18 : List Nat := [246, 247, 248, 250, 251, 252, 254, 255, 256, 258]
def hint0Block19 : List Nat := [259, 260, 262, 263, 264, 266, 267, 268, 270, 271]
def hint0Block20 : List Nat := [272, 274, 275, 276, 278, 279, 280, 282, 283, 284]
def hint0Block21 : List Nat := [286, 287, 288, 290, 291, 292, 294, 295, 296, 298]
def hint0Block22 : List Nat := [299, 300, 302, 303, 304, 306, 307, 308, 310, 311]
def hint0Block23 : List Nat := [312, 314, 315, 316, 318, 319, 320, 322, 323, 324]
def hint0Block24 : List Nat := [326, 327, 328]
def hints0 : List Nat := ((((hint0Block0 ++ (hint0Block1 ++ hint0Block2)) ++ (hint0Block3 ++ (hint0Block4 ++ hint0Block5))) ++ ((hint0Block6 ++ (hint0Block7 ++ hint0Block8)) ++ (hint0Block9 ++ (hint0Block10 ++ hint0Block11)))) ++ (((hint0Block12 ++ (hint0Block13 ++ hint0Block14)) ++ (hint0Block15 ++ (hint0Block16 ++ hint0Block17))) ++ ((hint0Block18 ++ (hint0Block19 ++ hint0Block20)) ++ ((hint0Block21 ++ hint0Block22) ++ (hint0Block23 ++ hint0Block24)))))
def step0 : Step := .del 736 hints0
def state1 : Known := next state0 step0
def hint1Block0 : List Nat := [383, 554, 21, 117, 382]
def hints1 : List Nat := hint1Block0
def step1 : Step := .add 737 [(105, false), (16, true), (88, true)] hints1
def state2 : Known := next state1 step1
def hint2Block0 : List Nat := [377, 551, 17, 113, 376]
def hints2 : List Nat := hint2Block0
def step2 : Step := .add 738 [(102, false), (13, true), (85, true)] hints2
def state3 : Known := next state2 step2
def hint3Block0 : List Nat := [385, 556, 21, 117, 380]
def hints3 : List Nat := hint3Block0
def step3 : Step := .add 739 [(107, false), (16, true), (88, true)] hints3
def state4 : Known := next state3 step3
def hint4Block0 : List Nat := [540, 543, 739, 738, 737, 141, 576, 137, 379, 553]
def hint4Block1 : List Nat := [17, 113, 374]
def hints4 : List Nat := (hint4Block0 ++ hint4Block1)
def step4 : Step := .add 740 [(82, false), (13, true), (16, true)] hints4
def state5 : Known := next state4 step4
def hint5Block0 : List Nat := [540, 543, 739, 738, 737, 576]
def hints5 : List Nat := hint5Block0
def step5 : Step := .del 740 hints5
def state6 : Known := next state5 step5
def hint6Block0 : List Nat := [365, 518, 9, 93, 364]
def hints6 : List Nat := hint6Block0
def step6 : Step := .add 741 [(96, false), (7, true), (70, true)] hints6
def state7 : Known := next state6 step6
def hint7Block0 : List Nat := [368, 371, 97, 133, 523]
def hints7 : List Nat := hint7Block0
def step7 : Step := .add 742 [(9, false), (73, true), (100, true)] hints7
def state8 : Known := next state7 step7
def hint8Block0 : List Nat := [742, 13, 370, 373, 97, 133, 521]
def hints8 : List Nat := hint8Block0
def step8 : Step := .add 743 [(100, true), (10, true), (73, true)] hints8
def state9 : Known := next state8 step8
def hint9Block0 : List Nat := [742]
def hints9 : List Nat := hint9Block0
def step9 : Step := .del 743 hints9
def state10 : Known := next state9 step9
def hint10Block0 : List Nat := [507, 510, 741, 743, 573, 129, 367, 520, 9, 93]
def hint10Block1 : List Nat := [362]
def hints10 : List Nat := (hint10Block0 ++ hint10Block1)
def step10 : Step := .add 744 [(67, false), (7, true), (10, true)] hints10
def state11 : Known := next state10 step10
def hint11Block0 : List Nat := [507, 510, 741, 743, 573]
def hints11 : List Nat := hint11Block0
def step11 : Step := .del 744 hints11
def state12 : Known := next state11 step11
def hint12Block0 : List Nat := [436, 439, 169, 177, 599]
def hints12 : List Nat := hint12Block0
def step12 : Step := .add 745 [(32, false), (127, true), (133, true)] hints12
def state13 : Known := next state12 step12
def hint13Block0 : List Nat := [745, 41, 434, 437, 169, 177, 601]
def hints13 : List Nat := hint13Block0
def step13 : Step := .add 746 [(133, true), (31, true), (127, true)] hints13
def state14 : Known := next state13 step13
def hint14Block0 : List Nat := [745]
def hints14 : List Nat := hint14Block0
def step14 : Step := .del 746 hints14
def state15 : Known := next state14 step14
def hint15Block0 : List Nat := [443, 602, 45, 173, 442]
def hints15 : List Nat := hint15Block0
def step15 : Step := .add 747 [(135, false), (34, true), (130, true)] hints15
def state16 : Known := next state15 step15
def hint16Block0 : List Nat := [534, 537, 746, 747, 606, 181, 445, 604, 45, 173]
def hint16Block1 : List Nat := [440]
def hints16 : List Nat := (hint16Block0 ++ hint16Block1)
def step16 : Step := .add 748 [(79, false), (31, true), (34, true)] hints16
def state17 : Known := next state16 step16
def hint17Block0 : List Nat := [534, 537, 746, 747, 606]
def hints17 : List Nat := hint17Block0
def step17 : Step := .del 748 hints17
def state18 : Known := next state17 step17
def hint18Block0 : List Nat := [589, 610, 153, 185, 584]
def hints18 : List Nat := hint18Block0
def step18 : Step := .add 749 [(146, false), (115, true), (139, true)] hints18
def state19 : Known := next state18 step18
def hint19Block0 : List Nat := [590, 593, 189, 197, 613]
def hints19 : List Nat := hint19Block0
def step19 : Step := .add 750 [(117, false), (142, true), (148, true)] hints19
def state20 : Known := next state19 step19
def hint20Block0 : List Nat := [584, 587, 185, 193, 568, 615, 125, 570, 750, 157]
def hint20Block1 : List Nat := [592, 595, 189, 197, 611]
def hints20 : List Nat := (hint20Block0 ++ hint20Block1)
def step20 : Step := .add 751 [(114, false), (93, true), (118, true), (139, true), (146, true)] hints20
def state21 : Known := next state20 step20
def hint21Block0 : List Nat := [431, 581, 37, 149, 430]
def hints21 : List Nat := hint21Block0
def step21 : Step := .add 752 [(123, false), (28, true), (112, true)] hints21
def state22 : Known := next state21 step21
def hint22Block0 : List Nat := [427, 580, 33, 145, 422]
def hints22 : List Nat := hint22Block0
def step22 : Step := .add 753 [(122, false), (25, true), (109, true)] hints22
def state23 : Known := next state22 step22
def hint23Block0 : List Nat := [753, 161, 425, 578, 33, 145, 424]
def hints23 : List Nat := hint23Block0
def step23 : Step := .add 754 [(109, true), (25, true), (121, true)] hints23
def state24 : Known := next state23 step23
def hint24Block0 : List Nat := [753]
def hints24 : List Nat := hint24Block0
def step24 : Step := .del 754 hints24
def state25 : Known := next state24 step24
def hint25Block0 : List Nat := [126, 567, 570, 749, 751, 153, 586, 185, 608, 193]
def hint25Block1 : List Nat := [615, 750, 157, 592, 595, 189, 197, 611]
def hints25 : List Nat := (hint25Block0 ++ hint25Block1)
def step25 : Step := .add 755 [(94, false), (115, true), (118, true)] hints25
def state26 : Known := next state25 step25
def hint26Block0 : List Nat := [126, 567, 570, 749, 751, 615, 750]
def hints26 : List Nat := hint26Block0
def step26 : Step := .del 755 hints26
def state27 : Known := next state26 step26
def hint27Block0 : List Nat := [561, 564, 754, 752, 597, 165, 433, 583, 37, 149]
def hint27Block1 : List Nat := [428]
def hints27 : List Nat := (hint27Block0 ++ hint27Block1)
def step27 : Step := .add 756 [(91, false), (25, true), (28, true)] hints27
def state28 : Known := next state27 step27
def hint28Block0 : List Nat := [561, 564, 754, 752, 597]
def hints28 : List Nat := hint28Block0
def step28 : Step := .del 756 hints28
def state29 : Known := next state28 step28
def hint29Block0 : List Nat := [375, 552, 17, 137, 379]
def hints29 : List Nat := hint29Block0
def step29 : Step := .add 757 [(85, false), (12, true), (102, true)] hints29
def state30 : Known := next state29 step29
def hint30Block0 : List Nat := [379]
def hints30 : List Nat := hint30Block0
def step30 : Step := .del 757 hints30
def state31 : Known := next state30 step30
def hint31Block0 : List Nat := [757, 113, 376, 17, 378, 137, 553]
def hints31 : List Nat := hint31Block0
def step31 : Step := .add 758 [(102, true), (12, true), (84, true)] hints31
def state32 : Known := next state31 step31
def hint32Block0 : List Nat := [757, 376, 553]
def hints32 : List Nat := hint32Block0
def step32 : Step := .del 758 hints32
def state33 : Known := next state32 step32
def hint33Block0 : List Nat := [381, 384, 117, 141, 556]
def hints33 : List Nat := hint33Block0
def step33 : Step := .add 759 [(16, false), (87, true), (105, true)] hints33
def state34 : Known := next state33 step33
def hint34Block0 : List Nat := [556]
def hints34 : List Nat := hint34Block0
def step34 : Step := .del 759 hints34
def state35 : Known := next state34 step34
def hint35Block0 : List Nat := [338, 341, 758, 575, 759, 21, 382, 117, 555, 141]
def hint35Block1 : List Nat := [385]
def hints35 : List Nat := (hint35Block0 ++ hint35Block1)
def step35 : Step := .add 760 [(0, false), (84, true), (87, true)] hints35
def state36 : Known := next state35 step35
def hint36Block0 : List Nat := [338, 341, 758, 575, 759, 382, 385]
def hints36 : List Nat := hint36Block0
def step36 : Step := .del 760 hints36
def state37 : Known := next state36 step36
def hint37Block0 : List Nat := [448, 451, 241, 249, 683]
def hints37 : List Nat := hint37Block0
def step37 : Step := .add 761 [(38, false), (181, true), (187, true)] hints37
def state38 : Known := next state37 step37
def hint38Block0 : List Nat := [761, 49, 446, 449, 241, 249, 685]
def hints38 : List Nat := hint38Block0
def step38 : Step := .add 762 [(187, true), (37, true), (181, true)] hints38
def state39 : Known := next state38 step38
def hint39Block0 : List Nat := [761]
def hints39 : List Nat := hint39Block0
def step39 : Step := .del 762 hints39
def state40 : Known := next state39 step39
def hint40Block0 : List Nat := [455, 686, 53, 245, 454]
def hints40 : List Nat := hint40Block0
def step40 : Step := .add 763 [(189, false), (40, true), (184, true)] hints40
def state41 : Known := next state40 step40
def hint41Block0 : List Nat := [387, 390, 762, 763, 690, 253, 457, 688, 53, 245]
def hint41Block1 : List Nat := [452]
def hints41 : List Nat := (hint41Block0 ++ hint41Block1)
def step41 : Step := .add 764 [(19, false), (37, true), (40, true)] hints41
def state42 : Known := next state41 step41
def hint42Block0 : List Nat := [387, 390, 762, 763, 690]
def hints42 : List Nat := hint42Block0
def step42 : Step := .del 764 hints42
def state43 : Known := next state42 step42
def hint43Block0 : List Nat := [503, 665, 85, 229, 502]
def hints43 : List Nat := hint43Block0
def step43 : Step := .add 766 [(201, false), (64, true), (172, true)] hints43
def state44 : Known := next state43 step43
def hint44Block0 : List Nat := [494, 662, 81, 265, 499]
def hints44 : List Nat := hint44Block0
def step44 : Step := .add 767 [(168, false), (61, true), (199, true)] hints44
def state45 : Known := next state44 step44
def hint45Block0 : List Nat := [767, 225, 496, 664, 81, 265, 497]
def hints45 : List Nat := hint45Block0
def step45 : Step := .add 768 [(199, true), (61, true), (169, true)] hints45
def state46 : Known := next state45 step45
def hint46Block0 : List Nat := [767]
def hints46 : List Nat := hint46Block0
def step46 : Step := .del 768 hints46
def state47 : Known := next state46 step46
def hint47Block0 : List Nat := [357, 360, 766, 768, 696, 269, 505, 667, 85, 229]
def hint47Block1 : List Nat := [500]
def hints47 : List Nat := (hint47Block0 ++ hint47Block1)
def step47 : Step := .add 769 [(4, false), (169, true), (172, true)] hints47
def state48 : Known := next state47 step47
def hint48Block0 : List Nat := [357, 360, 766, 768, 696]
def hints48 : List Nat := hint48Block0
def step48 : Step := .del 769 hints48
def state49 : Known := next state48 step48
def hint49Block0 : List Nat := [512, 524, 89, 105, 517]
def hints49 : List Nat := hint49Block0
def step49 : Step := .add 771 [(75, false), (67, true), (79, true)] hints49
def state50 : Known := next state49 step49
def hint50Block0 : List Nat := [550, 559, 109, 121, 545]
def hints50 : List Nat := hint50Block0
def step50 : Step := .add 772 [(95, false), (82, true), (91, true)] hints50
def state51 : Known := next state50 step50
def hint51Block0 : List Nat := [528, 531, 755]
def hints51 : List Nat := hint51Block0
def step51 : Step := .add 773 [(76, false), (94, false)] hints51
def state52 : Known := next state51 step51
def hint52Block0 : List Nat := [528, 531, 755]
def hints52 : List Nat := hint52Block0
def step52 : Step := .del 773 hints52
def state53 : Known := next state52 step52
def hint53Block0 : List Nat := [514, 526, 89, 105, 515]
def hints53 : List Nat := hint53Block0
def step53 : Step := .add 774 [(77, false), (67, true), (79, true)] hints53
def state54 : Known := next state53 step53
def hint54Block0 : List Nat := [333, 336, 339, 342, 744, 740, 774, 771, 101, 772]
def hint54Block1 : List Nat := [773, 125, 548, 557, 109, 121, 547]
def hints54 : List Nat := (hint54Block0 ++ hint54Block1)
def step54 : Step := .add 775 [(1, false), (79, true), (91, true)] hints54
def state55 : Known := next state54 step54
def hint55Block0 : List Nat := [333, 336, 339, 342, 744, 740, 774, 771, 772, 773]
def hints55 : List Nat := hint55Block0
def step55 : Step := .del 775 hints55
def state56 : Known := next state55 step55
def hint56Block0 : List Nat := [331, 349, 1, 25, 344]
def hints56 : List Nat := hint56Block0
def step56 : Step := .add 776 [(5, false), (1, true), (19, true)] hints56
def state57 : Known := next state56 step56
def hint57Block0 : List Nat := [329, 347, 1, 25, 346]
def hints57 : List Nat := hint57Block0
def step57 : Step := .add 778 [(3, false), (1, true), (19, true)] hints57
def state58 : Known := next state57 step57
def hint58Block0 : List Nat := [448, 241, 684, 249, 451]
def hints58 : List Nat := hint58Block0
def step58 : Step := .add 779 [(38, false), (180, true), (186, true)] hints58
def state59 : Known := next state58 step58
def hint59Block0 : List Nat := [448, 451]
def hints59 : List Nat := hint59Block0
def step59 : Step := .del 779 hints59
def state60 : Known := next state59 step59
def hint60Block0 : List Nat := [779, 49, 447, 450, 241, 249, 685]
def hints60 : List Nat := hint60Block0
def step60 : Step := .add 780 [(186, true), (36, true), (180, true)] hints60
def state61 : Known := next state60 step60
def hint61Block0 : List Nat := [779, 685]
def hints61 : List Nat := hint61Block0
def step61 : Step := .del 780 hints61
def state62 : Known := next state61 step61
def hint62Block0 : List Nat := [454, 245, 687, 253, 457]
def hints62 : List Nat := hint62Block0
def step62 : Step := .add 781 [(41, false), (183, true), (189, true)] hints62
def state63 : Known := next state62 step62
def hint63Block0 : List Nat := [454, 457]
def hints63 : List Nat := hint63Block0
def step63 : Step := .del 781 hints63
def state64 : Known := next state63 step63
def hint64Block0 : List Nat := [386, 389, 780, 689, 781, 53, 453, 456, 245, 253]
def hint64Block1 : List Nat := [688]
def hints64 : List Nat := (hint64Block0 ++ hint64Block1)
def step64 : Step := .add 782 [(18, false), (36, true), (39, true)] hints64
def state65 : Known := next state64 step64
def hint65Block0 : List Nat := [386, 389, 780, 689, 781, 688]
def hints65 : List Nat := hint65Block0
def step65 : Step := .del 782 hints65
def state66 : Known := next state65 step65
def hint66Block0 : List Nat := [364, 93, 519, 129, 367]
def hints66 : List Nat := hint66Block0
def step66 : Step := .add 783 [(8, false), (69, true), (96, true)] hints66
def state67 : Known := next state66 step66
def hint67Block0 : List Nat := [364, 367]
def hints67 : List Nat := hint67Block0
def step67 : Step := .del 783 hints67
def state68 : Known := next state67 step67
def hint68Block0 : List Nat := [783, 9, 363, 366, 93, 129, 520]
def hints68 : List Nat := hint68Block0
def step68 : Step := .add 784 [(96, true), (6, true), (69, true)] hints68
def state69 : Known := next state68 step68
def hint69Block0 : List Nat := [783, 520]
def hints69 : List Nat := hint69Block0
def step69 : Step := .del 784 hints69
def state70 : Known := next state69 step69
def hint70Block0 : List Nat := [370, 97, 522, 133, 373]
def hints70 : List Nat := hint70Block0
def step70 : Step := .add 785 [(11, false), (72, true), (99, true)] hints70
def state71 : Known := next state70 step70
def hint71Block0 : List Nat := [370, 373]
def hints71 : List Nat := hint71Block0
def step71 : Step := .del 785 hints71
def state72 : Known := next state71 step71
def hint72Block0 : List Nat := [506, 509, 784, 572, 785, 13, 369, 372, 97, 133]
def hint72Block1 : List Nat := [523]
def hints72 : List Nat := (hint72Block0 ++ hint72Block1)
def step72 : Step := .add 786 [(66, false), (6, true), (9, true)] hints72
def state73 : Known := next state72 step72
def hint73Block0 : List Nat := [506, 509, 784, 572, 785, 523]
def hints73 : List Nat := hint73Block0
def step73 : Step := .del 786 hints73
def state74 : Known := next state73 step73
def hint74Block0 : List Nat := [586, 185, 609, 193, 589]
def hints74 : List Nat := hint74Block0
def step74 : Step := .add 787 [(116, false), (138, true), (144, true)] hints74
def state75 : Known := next state74 step74
def hint75Block0 : List Nat := [586, 589]
def hints75 : List Nat := hint75Block0
def step75 : Step := .del 787 hints75
def state76 : Known := next state75 step75
def hint76Block0 : List Nat := [787, 153, 585, 588, 185, 193, 610]
def hints76 : List Nat := hint76Block0
def step76 : Step := .add 788 [(144, true), (114, true), (138, true)] hints76
def state77 : Known := next state76 step76
def hint77Block0 : List Nat := [787, 610]
def hints77 : List Nat := hint77Block0
def step77 : Step := .del 788 hints77
def state78 : Known := next state77 step77
def hint78Block0 : List Nat := [592, 189, 612, 197, 595]
def hints78 : List Nat := hint78Block0
def step78 : Step := .add 789 [(119, false), (141, true), (147, true)] hints78
def state79 : Known := next state78 step78
def hint79Block0 : List Nat := [592, 595]
def hints79 : List Nat := hint79Block0
def step79 : Step := .del 789 hints79
def state80 : Known := next state79 step79
def hint80Block0 : List Nat := [566, 569, 788, 614, 789, 157, 591, 594, 189, 197]
def hint80Block1 : List Nat := [613]
def hints80 : List Nat := (hint80Block0 ++ hint80Block1)
def step80 : Step := .add 790 [(93, false), (114, true), (117, true)] hints80
def state81 : Known := next state80 step80
def hint81Block0 : List Nat := [566, 569, 788, 614, 789, 613]
def hints81 : List Nat := hint81Block0
def step81 : Step := .del 790 hints81
def state82 : Known := next state81 step81
def hint82Block0 : List Nat := [539, 542, 760]
def hints82 : List Nat := hint82Block0
def step82 : Step := .add 792 [(81, false), (0, false)] hints82
def state83 : Known := next state82 step82
def hint83Block0 : List Nat := [539, 542, 760]
def hints83 : List Nat := hint83Block0
def step83 : Step := .del 792 hints83
def state84 : Known := next state83 step83
def hint84Block0 : List Nat := [547, 109, 549, 125, 559]
def hints84 : List Nat := hint84Block0
def step84 : Step := .add 793 [(92, false), (81, true), (93, true)] hints84
def state85 : Known := next state84 step84
def hint85Block0 : List Nat := [547, 559]
def hints85 : List Nat := hint85Block0
def step85 : Step := .del 793 hints85
def state86 : Known := next state85 step85
def hint86Block0 : List Nat := [429, 582, 560, 37, 145, 433, 579, 165, 161, 596]
def hints86 : List Nat := hint86Block0
def step86 : Step := .add 794 [(112, false), (27, true), (90, false), (110, true), (122, true)] hints86
def state87 : Known := next state86 step86
def hint87Block0 : List Nat := [423, 579, 563, 33, 424, 427, 161, 596, 794, 149]
def hint87Block1 : List Nat := [430, 583, 37, 165, 432]
def hints87 : List Nat := (hint87Block0 ++ hint87Block1)
def step87 : Step := .add 795 [(109, false), (24, true), (27, true), (90, false)] hints87
def state88 : Known := next state87 step87
def hint88Block0 : List Nat := [427, 794]
def hints88 : List Nat := hint88Block0
def step88 : Step := .del 795 hints88
def state89 : Known := next state88 step88
def hint89Block0 : List Nat := [432, 582, 37, 149, 430]
def hints89 : List Nat := hint89Block0
def step89 : Step := .add 796 [(124, false), (27, true), (111, true)] hints89
def state90 : Known := next state89 step89
def hint90Block0 : List Nat := [430]
def hints90 : List Nat := hint90Block0
def step90 : Step := .del 796 hints90
def state91 : Known := next state90 step90
def hint91Block0 : List Nat := [560, 563, 795, 145, 796, 424, 33, 426, 580, 161]
def hint91Block1 : List Nat := [596, 165, 433, 37, 429, 149, 583]
def hints91 : List Nat := (hint91Block0 ++ hint91Block1)
def step91 : Step := .add 797 [(90, false), (24, true), (27, true)] hints91
def state92 : Known := next state91 step91
def hint92Block0 : List Nat := [560, 563, 795, 796, 424, 580, 596, 433, 583]
def hints92 : List Nat := hint92Block0
def step92 : Step := .del 797 hints92
def state93 : Known := next state92 step92
def hint93Block0 : List Nat := [436, 169, 600, 177, 439]
def hints93 : List Nat := hint93Block0
def step93 : Step := .add 798 [(32, false), (126, true), (132, true)] hints93
def state94 : Known := next state93 step93
def hint94Block0 : List Nat := [436, 439]
def hints94 : List Nat := hint94Block0
def step94 : Step := .del 798 hints94
def state95 : Known := next state94 step94
def hint95Block0 : List Nat := [798, 41, 435, 438, 169, 177, 601]
def hints95 : List Nat := hint95Block0
def step95 : Step := .add 799 [(132, true), (30, true), (126, true)] hints95
def state96 : Known := next state95 step95
def hint96Block0 : List Nat := [798, 601]
def hints96 : List Nat := hint96Block0
def step96 : Step := .del 799 hints96
def state97 : Known := next state96 step96
def hint97Block0 : List Nat := [442, 173, 603, 181, 445]
def hints97 : List Nat := hint97Block0
def step97 : Step := .add 800 [(35, false), (129, true), (135, true)] hints97
def state98 : Known := next state97 step97
def hint98Block0 : List Nat := [442, 445]
def hints98 : List Nat := hint98Block0
def step98 : Step := .del 800 hints98
def state99 : Known := next state98 step98
def hint99Block0 : List Nat := [533, 536, 799, 605, 800, 45, 441, 444, 173, 181]
def hint99Block1 : List Nat := [604]
def hints99 : List Nat := (hint99Block0 ++ hint99Block1)
def step99 : Step := .add 801 [(78, false), (30, true), (33, true)] hints99
def state100 : Known := next state99 step99
def hint100Block0 : List Nat := [533, 536, 799, 605, 800, 604]
def hints100 : List Nat := hint100Block0
def step100 : Step := .del 801 hints100
def state101 : Known := next state100 step100
def hint101Block0 : List Nat := [332, 335, 786]
def hints101 : List Nat := hint101Block0
def step101 : Step := .add 802 [(0, false), (66, false)] hints101
def state102 : Known := next state101 step101
def hint102Block0 : List Nat := [332, 335, 786]
def hints102 : List Nat := hint102Block0
def step102 : Step := .del 802 hints102
def state103 : Known := next state102 step102
def hint103Block0 : List Nat := [495, 663, 81, 265, 499]
def hints103 : List Nat := hint103Block0
def step103 : Step := .add 803 [(169, false), (60, true), (198, true)] hints103
def state104 : Known := next state103 step103
def hint104Block0 : List Nat := [499]
def hints104 : List Nat := hint104Block0
def step104 : Step := .del 803 hints104
def state105 : Known := next state104 step104
def hint105Block0 : List Nat := [803, 225, 496, 81, 498, 265, 664]
def hints105 : List Nat := hint105Block0
def step105 : Step := .add 804 [(198, true), (60, true), (168, true)] hints105
def state106 : Known := next state105 step105
def hint106Block0 : List Nat := [803, 496, 664]
def hints106 : List Nat := hint106Block0
def step106 : Step := .del 804 hints106
def state107 : Known := next state106 step106
def hint107Block0 : List Nat := [502, 85, 504, 269, 667]
def hints107 : List Nat := hint107Block0
def step107 : Step := .add 805 [(173, false), (63, true), (201, true)] hints107
def state108 : Known := next state107 step107
def hint108Block0 : List Nat := [502, 667]
def hints108 : List Nat := hint108Block0
def step108 : Step := .del 805 hints108
def state109 : Known := next state108 step108
def hint109Block0 : List Nat := [356, 359, 804, 695, 805, 229, 501, 666, 85, 269]
def hint109Block1 : List Nat := [505]
def hints109 : List Nat := (hint109Block0 ++ hint109Block1)
def step109 : Step := .add 806 [(3, false), (168, true), (171, true)] hints109
def state110 : Known := next state109 step109
def hint110Block0 : List Nat := [356, 359, 804, 695, 805, 505]
def hints110 : List Nat := hint110Block0
def step110 : Step := .del 806 hints110
def state111 : Known := next state110 step110
def hint111Block0 : List Nat := [527, 530, 790]
def hints111 : List Nat := hint111Block0
def step111 : Step := .add 808 [(75, false), (93, false)] hints111
def state112 : Known := next state111 step111
def hint112Block0 : List Nat := [527, 530, 790]
def hints112 : List Nat := hint112Block0
def step112 : Step := .del 808 hints112
def state113 : Known := next state112 step112
def hint113Block0 : List Nat := [516, 525, 89, 101, 514]
def hints113 : List Nat := hint113Block0
def step113 : Step := .add 809 [(79, false), (66, true), (75, true)] hints113
def state114 : Known := next state113 step113
def hint114Block0 : List Nat := [514]
def hints114 : List Nat := hint114Block0
def step114 : Step := .del 809 hints114
def state115 : Known := next state114 step114
def hint115Block0 : List Nat := [809, 105, 517, 89, 513, 101, 526]
def hints115 : List Nat := hint115Block0
def step115 : Step := .add 810 [(75, true), (66, true), (78, true)] hints115
def state116 : Known := next state115 step115
def hint116Block0 : List Nat := [809, 517, 526]
def hints116 : List Nat := hint116Block0
def step116 : Step := .del 810 hints116
def state117 : Known := next state116 step116
def hint117Block0 : List Nat := [802, 792, 810, 808, 793, 121, 546, 558, 109, 125]
def hint117Block1 : List Nat := [550]
def hints117 : List Nat := (hint117Block0 ++ hint117Block1)
def step117 : Step := .add 811 [(0, false), (78, true), (90, true)] hints117
def state118 : Known := next state117 step117
def hint118Block0 : List Nat := [802, 792, 810, 808, 793, 550]
def hints118 : List Nat := hint118Block0
def step118 : Step := .del 811 hints118
def state119 : Known := next state118 step118
def hint119Block0 : List Nat := [331, 1, 345, 25, 349]
def hints119 : List Nat := hint119Block0
def step119 : Step := .add 812 [(5, false), (0, true), (18, true)] hints119
def state120 : Known := next state119 step119
def hint120Block0 : List Nat := [331, 349]
def hints120 : List Nat := hint120Block0
def step120 : Step := .del 812 hints120
def state121 : Known := next state120 step120
def hint121Block0 : List Nat := [657, 675, 221, 277, 650, 653, 466, 806, 61, 414]
def hint121Block1 : List Nat := [29, 392, 395, 398, 401, 404, 407, 797, 801, 782]
def hint121Block2 : List Nat := [811, 812, 5, 330, 348, 1, 25, 346]
def hints121 : List Nat := (hint121Block0 ++ (hint121Block1 ++ hint121Block2))
def step121 : Step := .add 813 [(175, false), (23, true), (45, true), (167, true), (207, true)] hints121
def state122 : Known := next state121 step121
def hint122Block0 : List Nat := [460, 463, 671, 273, 289, 699]
def hints122 : List Nat := hint122Block0
def step122 : Step := .add 814 [(44, false), (167, true), (174, false), (216, true)] hints122
def state123 : Known := next state122 step122
def hint123Block0 : List Nat := [393, 396, 756]
def hints123 : List Nat := hint123Block0
def step123 : Step := .add 815 [(22, false), (91, false)] hints123
def state124 : Known := next state123 step123
def hint124Block0 : List Nat := [393, 396, 756]
def hints124 : List Nat := hint124Block0
def step124 : Step := .del 815 hints124
def state125 : Known := next state124 step124
def hint125Block0 : List Nat := [459, 462, 273, 289, 700]
def hints125 : List Nat := hint125Block0
def step125 : Step := .add 816 [(43, false), (204, true), (216, true)] hints125
def state126 : Known := next state125 step125
def hint126Block0 : List Nat := [467, 701, 716, 813, 233, 656, 671, 221, 816, 651]
def hint126Block1 : List Nat := [654, 769, 814, 57, 410, 29, 399, 402, 405, 408]
def hint126Block2 : List Nat := [815, 748, 764, 775, 776, 778, 5]
def hints126 : List Nat := (hint126Block0 ++ (hint126Block1 ++ hint126Block2))
def step126 : Step := .add 817 [(219, false), (23, true), (167, true), (176, true)] hints126
def state127 : Known := next state126 step126
def hint127Block0 : List Nat := [813, 814]
def hints127 : List Nat := hint127Block0
def step127 : Step := .del 817 hints127
def state128 : Known := next state127 step127
def hint128Block0 : List Nat := [651, 654, 769]
def hints128 : List Nat := hint128Block0
def step128 : Step := .add 818 [(166, false), (4, false)] hints128
def state129 : Known := next state128 step128
def hint129Block0 : List Nat := [651, 654, 769]
def hints129 : List Nat := hint129Block0
def step129 : Step := .del 818 hints129
def state130 : Known := next state129 step129
def hint130Block0 : List Nat := [469, 703, 61, 277, 464]
def hints130 : List Nat := hint130Block0
def step130 : Step := .add 819 [(221, false), (46, true), (208, true)] hints130
def state131 : Known := next state130 step130
def hint131Block0 : List Nat := [463, 57, 458, 273, 700]
def hints131 : List Nat := hint131Block0
def step131 : Step := .add 820 [(218, false), (43, true), (205, true)] hints131
def state132 : Known := next state131 step131
def hint132Block0 : List Nat := [700]
def hints132 : List Nat := hint132Block0
def step132 : Step := .del 820 hints132
def state133 : Known := next state132 step132
def hint133Block0 : List Nat := [392, 395, 398, 401, 404, 407, 797, 801, 782, 811]
def hint133Block1 : List Nat := [25, 1, 346]
def hints133 : List Nat := (hint133Block0 ++ hint133Block1)
def step133 : Step := .add 821 [(21, false), (1, true), (19, true)] hints133
def state134 : Known := next state133 step133
def hint134Block0 : List Nat := [346]
def hints134 : List Nat := hint134Block0
def step134 : Step := .del 821 hints134
def state135 : Known := next state134 step134
def hint135Block0 : List Nat := [399, 402, 405, 408, 815, 748, 764, 775, 776, 5]
def hint135Block1 : List Nat := [778]
def hints135 : List Nat := (hint135Block0 ++ hint135Block1)
def step135 : Step := .add 823 [(22, false), (4, true)] hints135
def state136 : Known := next state135 step135
def hint136Block0 : List Nat := [399, 402, 405, 408, 815, 748, 764, 775, 776, 778]
def hints136 : List Nat := hint136Block0
def step136 : Step := .del 823 hints136
def state137 : Known := next state136 step136
def hint137Block0 : List Nat := [650, 653, 806]
def hints137 : List Nat := hint137Block0
def step137 : Step := .add 824 [(165, false), (3, false)] hints137
def state138 : Known := next state137 step137
def hint138Block0 : List Nat := [650, 653, 806]
def hints138 : List Nat := hint138Block0
def step138 : Step := .del 824 hints138
def state139 : Known := next state138 step138
def hint139Block0 : List Nat := [468, 702, 61, 277, 466]
def hints139 : List Nat := hint139Block0
def step139 : Step := .add 825 [(220, false), (45, true), (207, true)] hints139
def state140 : Known := next state139 step139
def hint140Block0 : List Nat := [823, 817, 29, 392, 395, 398, 401, 404, 407, 413]
def hint140Block1 : List Nat := [797, 801, 782, 811, 812, 5, 824, 221, 657, 233]
def hint140Block2 : List Nat := [674, 825, 293, 469, 703, 61, 277, 465]
def hints140 : List Nat := (hint140Block0 ++ (hint140Block1 ++ hint140Block2))
def step140 : Step := .add 826 [(4, true), (23, true), (167, true), (176, true)] hints140
def state141 : Known := next state140 step140
def hint141Block0 : List Nat := [826, 330, 348, 818, 821, 221, 29, 656, 411, 414]
def hint141Block1 : List Nat := [233, 672, 675, 820, 819, 817, 293, 717, 289, 461]
def hint141Block2 : List Nat := [698, 57, 273, 460]
def hints141 : List Nat := (hint141Block0 ++ (hint141Block1 ++ hint141Block2))
def step141 : Step := .add 827 [(23, true), (167, true), (176, true)] hints141
def state142 : Known := next state141 step141
def hint142Block0 : List Nat := [826, 817]
def hints142 : List Nat := hint142Block0
def step142 : Step := .del 827 hints142
def state143 : Known := next state142 step142
def hint143Block0 : List Nat := [535, 538, 173, 169, 602, 599, 181, 177, 607]
def hints143 : List Nat := hint143Block0
def step143 : Step := .add 829 [(80, false), (127, true), (130, true), (133, true), (136, true)] hints143
def state144 : Known := next state143 step143
def hint144Block0 : List Nat := [369, 97, 372, 133, 521]
def hints144 : List Nat := hint144Block0
def step144 : Step := .add 830 [(10, false), (74, true), (101, true)] hints144
def state145 : Known := next state144 step144
def hint145Block0 : List Nat := [369, 372, 521]
def hints145 : List Nat := hint145Block0
def step145 : Step := .del 830 hints145
def state146 : Known := next state145 step145
def hint146Block0 : List Nat := [830, 13, 368, 371, 97, 133, 522]
def hints146 : List Nat := hint146Block0
def step146 : Step := .add 831 [(101, true), (11, true), (74, true)] hints146
def state147 : Known := next state146 step146
def hint147Block0 : List Nat := [830, 13, 368, 371, 97, 133, 522]
def hints147 : List Nat := hint147Block0
def step147 : Step := .del 831 hints147
def state148 : Known := next state147 step147
def hint148Block0 : List Nat := [363, 93, 366, 129, 518]
def hints148 : List Nat := hint148Block0
def step148 : Step := .add 832 [(7, false), (71, true), (98, true)] hints148
def state149 : Known := next state148 step148
def hint149Block0 : List Nat := [363, 366, 518]
def hints149 : List Nat := hint149Block0
def step149 : Step := .del 832 hints149
def state150 : Known := next state149 step149
def hint150Block0 : List Nat := [508, 511, 831, 574, 832, 9, 362, 365, 93, 129]
def hint150Block1 : List Nat := [519]
def hints150 : List Nat := (hint150Block0 ++ hint150Block1)
def step150 : Step := .add 833 [(68, false), (8, true), (11, true)] hints150
def state151 : Known := next state150 step150
def hint151Block0 : List Nat := [508, 511, 831, 574, 832, 9, 362, 365, 93, 129]
def hint151Block1 : List Nat := [519]
def hints151 : List Nat := (hint151Block0 ++ hint151Block1)
def step151 : Step := .del 833 hints151
def state152 : Known := next state151 step151
def hint152Block0 : List Nat := [591, 189, 594, 197, 611]
def hints152 : List Nat := hint152Block0
def step152 : Step := .add 834 [(118, false), (143, true), (149, true)] hints152
def state153 : Known := next state152 step152
def hint153Block0 : List Nat := [591, 594, 611]
def hints153 : List Nat := hint153Block0
def step153 : Step := .del 834 hints153
def state154 : Known := next state153 step153
def hint154Block0 : List Nat := [834, 157, 590, 593, 189, 197, 612]
def hints154 : List Nat := hint154Block0
def step154 : Step := .add 835 [(149, true), (119, true), (143, true)] hints154
def state155 : Known := next state154 step154
def hint155Block0 : List Nat := [834, 157, 590, 593, 189, 197, 612]
def hints155 : List Nat := hint155Block0
def step155 : Step := .del 835 hints155
def state156 : Known := next state155 step155
def hint156Block0 : List Nat := [585, 185, 588, 193, 608]
def hints156 : List Nat := hint156Block0
def step156 : Step := .add 836 [(115, false), (140, true), (146, true)] hints156
def state157 : Known := next state156 step156
def hint157Block0 : List Nat := [585, 588, 608]
def hints157 : List Nat := hint157Block0
def step157 : Step := .del 836 hints157
def state158 : Known := next state157 step157
def hint158Block0 : List Nat := [568, 571, 835, 616, 836, 153, 584, 587, 185, 193]
def hint158Block1 : List Nat := [609]
def hints158 : List Nat := (hint158Block0 ++ hint158Block1)
def step158 : Step := .add 837 [(95, false), (116, true), (119, true)] hints158
def state159 : Known := next state158 step158
def hint159Block0 : List Nat := [568, 571, 835, 616, 836, 153, 584, 587, 185, 193]
def hint159Block1 : List Nat := [609]
def hints159 : List Nat := (hint159Block0 ++ hint159Block1)
def step159 : Step := .del 837 hints159
def state160 : Known := next state159 step159
def hint160Block0 : List Nat := [375, 17, 552, 137, 377]
def hints160 : List Nat := hint160Block0
def step160 : Step := .add 838 [(85, false), (14, true), (104, true)] hints160
def state161 : Known := next state160 step160
def hint161Block0 : List Nat := [375, 552, 377]
def hints161 : List Nat := hint161Block0
def step161 : Step := .del 838 hints161
def state162 : Known := next state161 step161
def hint162Block0 : List Nat := [838, 113, 374, 551, 17, 137, 378]
def hints162 : List Nat := hint162Block0
def step162 : Step := .add 839 [(104, true), (14, true), (86, true)] hints162
def state163 : Known := next state162 step162
def hint163Block0 : List Nat := [838, 113, 374, 551, 17, 137, 378]
def hints163 : List Nat := hint163Block0
def step163 : Step := .del 839 hints163
def state164 : Known := next state163 step163
def hint164Block0 : List Nat := [381, 21, 555, 141, 383]
def hints164 : List Nat := hint164Block0
def step164 : Step := .add 840 [(88, false), (17, true), (107, true)] hints164
def state165 : Known := next state164 step164
def hint165Block0 : List Nat := [381, 555, 383]
def hints165 : List Nat := hint165Block0
def step165 : Step := .del 840 hints165
def state166 : Known := next state165 step165
def hint166Block0 : List Nat := [541, 544, 839, 577, 840, 117, 380, 554, 21, 141]
def hint166Block1 : List Nat := [384]
def hints166 : List Nat := (hint166Block0 ++ hint166Block1)
def step166 : Step := .add 841 [(83, false), (14, true), (17, true)] hints166
def state167 : Known := next state166 step166
def hint167Block0 : List Nat := [541, 544, 839, 577, 840, 117, 380, 554, 21, 141]
def hint167Block1 : List Nat := [384]
def hints167 : List Nat := (hint167Block0 ++ hint167Block1)
def step167 : Step := .del 841 hints167
def state168 : Known := next state167 step167
def hint168Block0 : List Nat := [562, 565, 145, 149, 422, 578, 581, 33, 165, 426]
def hint168Block1 : List Nat := [598, 161]
def hints168 : List Nat := (hint168Block0 ++ hint168Block1)
def step168 : Step := .add 842 [(109, true), (26, true), (92, false), (112, true), (124, true)] hints168
def state169 : Known := next state168 step168
def hint169Block0 : List Nat := [565, 149, 428, 37, 581, 432, 165, 598, 842, 423]
def hint169Block1 : List Nat := [579, 33, 161, 425]
def hints169 : List Nat := (hint169Block0 ++ hint169Block1)
def step169 : Step := .add 843 [(112, true), (26, true), (29, true), (92, false)] hints169
def state170 : Known := next state169 step169
def hint170Block0 : List Nat := [565, 149, 428, 581, 432, 842]
def hints170 : List Nat := hint170Block0
def step170 : Step := .del 843 hints170
def state171 : Known := next state170 step170
def hint171Block0 : List Nat := [425, 33, 578, 145, 423]
def hints171 : List Nat := hint171Block0
def step171 : Step := .add 844 [(120, false), (26, true), (110, true)] hints171
def state172 : Known := next state171 step171
def hint172Block0 : List Nat := [425, 578, 423]
def hints172 : List Nat := hint172Block0
def step172 : Step := .del 844 hints172
def state173 : Known := next state172 step172
def hint173Block0 : List Nat := [562, 843, 844, 429, 582, 37, 431, 165, 598, 161]
def hint173Block1 : List Nat := [426, 579, 33, 145, 422]
def hints173 : List Nat := (hint173Block0 ++ hint173Block1)
def step173 : Step := .add 845 [(92, false), (26, true), (29, true)] hints173
def state174 : Known := next state173 step173
def hint174Block0 : List Nat := [562, 843, 844, 429, 582, 37, 431, 165, 598, 161]
def hint174Block1 : List Nat := [426, 579, 33, 145, 422]
def hints174 : List Nat := (hint174Block0 ++ hint174Block1)
def step174 : Step := .del 845 hints174
def state175 : Known := next state174 step174
def hint175Block0 : List Nat := [444, 45, 603, 173, 440]
def hints175 : List Nat := hint175Block0
def step175 : Step := .add 847 [(136, false), (35, true), (131, true)] hints175
def state176 : Known := next state175 step175
def hint176Block0 : List Nat := [444, 603, 440]
def hints176 : List Nat := hint176Block0
def step176 : Step := .del 847 hints176
def state177 : Known := next state176 step176
def hint177Block0 : List Nat := [538, 173, 829, 435, 41, 437, 177, 607, 181, 602]
def hints177 : List Nat := hint177Block0
def step177 : Step := .add 848 [(133, true), (32, true), (80, false), (130, true), (136, true)] hints177
def state178 : Known := next state177 step177
def hint178Block0 : List Nat := [173, 829, 602]
def hints178 : List Nat := hint178Block0
def step178 : Step := .del 848 hints178
def state179 : Known := next state178 step178
def hint179Block0 : List Nat := [438, 41, 600, 169, 434]
def hints179 : List Nat := hint179Block0
def step179 : Step := .add 849 [(133, false), (32, true), (128, true)] hints179
def state180 : Known := next state179 step179
def hint180Block0 : List Nat := [438, 600, 434]
def hints180 : List Nat := hint180Block0
def step180 : Step := .del 849 hints180
def state181 : Known := next state180 step180
def hint181Block0 : List Nat := [535, 538, 849, 847, 848, 441, 45, 443, 181, 607]
def hint181Block1 : List Nat := [177, 437, 599, 41, 169, 435]
def hints181 : List Nat := (hint181Block0 ++ hint181Block1)
def step181 : Step := .add 850 [(80, false), (32, true), (35, true)] hints181
def state182 : Known := next state181 step181
def hint182Block0 : List Nat := [535, 538, 849, 847, 848, 441, 45, 443, 181, 607]
def hint182Block1 : List Nat := [177, 437, 599, 41, 169, 435]
def hints182 : List Nat := (hint182Block0 ++ hint182Block1)
def step182 : Step := .del 850 hints182
def state183 : Known := next state182 step182
def hint183Block0 : List Nat := [452, 245, 455, 253, 687]
def hints183 : List Nat := hint183Block0
def step183 : Step := .add 852 [(39, false), (185, true), (191, true)] hints183
def state184 : Known := next state183 step183
def hint184Block0 : List Nat := [452, 455, 687]
def hints184 : List Nat := hint184Block0
def step184 : Step := .del 852 hints184
def state185 : Known := next state184 step184
def hint185Block0 : List Nat := [852, 53, 453, 456, 245, 253, 686]
def hints185 : List Nat := hint185Block0
def step185 : Step := .add 853 [(191, true), (41, true), (185, true)] hints185
def state186 : Known := next state185 step185
def hint186Block0 : List Nat := [852, 53, 453, 456, 245, 253, 686]
def hints186 : List Nat := hint186Block0
def step186 : Step := .del 853 hints186
def state187 : Known := next state186 step186
def hint187Block0 : List Nat := [447, 241, 450, 249, 683]
def hints187 : List Nat := hint187Block0
def step187 : Step := .add 854 [(37, false), (182, true), (188, true)] hints187
def state188 : Known := next state187 step187
def hint188Block0 : List Nat := [447, 450, 683]
def hints188 : List Nat := hint188Block0
def step188 : Step := .del 854 hints188
def state189 : Known := next state188 step188
def hint189Block0 : List Nat := [388, 391, 853, 691, 854, 49, 446, 449, 241, 249]
def hint189Block1 : List Nat := [684]
def hints189 : List Nat := (hint189Block0 ++ hint189Block1)
def step189 : Step := .add 855 [(20, false), (38, true), (41, true)] hints189
def state190 : Known := next state189 step189
def hint190Block0 : List Nat := [388, 391, 853, 691, 854, 49, 446, 449, 241, 249]
def hint190Block1 : List Nat := [684]
def hints190 : List Nat := (hint190Block0 ++ hint190Block1)
def step190 : Step := .del 855 hints190
def state191 : Known := next state190 step190
def hint191Block0 : List Nat := [477, 480, 301, 309, 722]
def hints191 : List Nat := hint191Block0
def step191 : Step := .add 856 [(52, false), (227, true), (233, true)] hints191
def state192 : Known := next state191 step191
def hint192Block0 : List Nat := [646, 649, 297, 720, 305, 727, 856, 69, 476, 479]
def hint192Block1 : List Nat := [301, 309, 723]
def hints192 : List Nat := (hint192Block0 ++ hint192Block1)
def step192 : Step := .add 857 [(164, false), (53, true), (222, true), (228, true)] hints192
def state193 : Known := next state192 step192
def hint193Block0 : List Nat := [476, 479, 301, 309, 724]
def hints193 : List Nat := hint193Block0
def step193 : Step := .add 858 [(51, false), (226, true), (232, true)] hints193
def state194 : Known := next state193 step193
def hint194Block0 : List Nat := [489, 492, 209, 261, 632]
def hints194 : List Nat := hint194Block0
def step194 : Step := .add 859 [(58, false), (158, true), (197, true)] hints194
def state195 : Known := next state194 step194
def hint195Block0 : List Nat := [859, 77, 488, 491, 209, 261, 633]
def hints195 : List Nat := hint195Block0
def step195 : Step := .add 860 [(197, true), (59, true), (158, true)] hints195
def state196 : Known := next state195 step195
def hint196Block0 : List Nat := [859]
def hints196 : List Nat := hint196Block0
def step196 : Step := .del 860 hints196
def state197 : Known := next state196 step196
def hint197Block0 : List Nat := [483, 486, 205, 257, 629]
def hints197 : List Nat := hint197Block0
def step197 : Step := .add 861 [(55, false), (155, true), (194, true)] hints197
def state198 : Known := next state197 step197
def hint198Block0 : List Nat := [619, 622, 860, 694, 861, 73, 482, 485, 205, 257]
def hint198Block1 : List Nat := [630]
def hints198 : List Nat := (hint198Block0 ++ hint198Block1)
def step198 : Step := .add 862 [(152, false), (56, true), (59, true)] hints198
def state199 : Known := next state198 step198
def hint199Block0 : List Nat := [619, 622, 860, 694, 861]
def hints199 : List Nat := hint199Block0
def step199 : Step := .del 862 hints199
def state200 : Known := next state199 step199
def hint200Block0 : List Nat := [857, 473, 65, 471, 297, 646]
def hints200 : List Nat := hint200Block0
def step200 : Step := .add 864 [(222, true), (50, true), (53, true), (164, false)] hints200
def state201 : Known := next state200 step200
def hint201Block0 : List Nat := [857, 646]
def hints201 : List Nat := hint201Block0
def step201 : Step := .del 864 hints201
def state202 : Known := next state201 step201
def hint202Block0 : List Nat := [649, 864, 470, 719, 65, 474, 305, 727, 856, 69]
def hint202Block1 : List Nat := [476, 301, 723, 309, 479]
def hints202 : List Nat := (hint202Block0 ++ hint202Block1)
def step202 : Step := .add 865 [(164, false), (50, true), (53, true)] hints202
def state203 : Known := next state202 step202
def hint203Block0 : List Nat := [649, 864, 727, 856, 476, 479]
def hints203 : List Nat := hint203Block0
def step203 : Step := .del 865 hints203
def state204 : Known := next state203 step203
def hint204Block0 : List Nat := [545, 109, 557, 125, 549]
def hints204 : List Nat := hint204Block0
def step204 : Step := .add 866 [(90, false), (83, true), (95, true)] hints204
def state205 : Known := next state204 step204
def hint205Block0 : List Nat := [545, 557, 549]
def hints205 : List Nat := hint205Block0
def step205 : Step := .del 866 hints205
def state206 : Known := next state205 step205
def hint206Block0 : List Nat := [866, 121, 546, 558, 109, 125, 548]
def hints206 : List Nat := hint206Block0
def step206 : Step := .add 867 [(95, true), (83, true), (92, true)] hints206
def state207 : Known := next state206 step206
def hint207Block0 : List Nat := [866, 121, 546, 558, 109, 125, 548]
def hints207 : List Nat := hint207Block0
def step207 : Step := .del 867 hints207
def state208 : Known := next state207 step207
def hint208Block0 : List Nat := [529, 532, 837]
def hints208 : List Nat := hint208Block0
def step208 : Step := .add 868 [(77, false), (95, false)] hints208
def state209 : Known := next state208 step208
def hint209Block0 : List Nat := [529, 532, 837]
def hints209 : List Nat := hint209Block0
def step209 : Step := .del 868 hints209
def state210 : Known := next state209 step209
def hint210Block0 : List Nat := [515, 89, 524, 101, 513]
def hints210 : List Nat := hint210Block0
def step210 : Step := .add 869 [(78, false), (68, true), (77, true)] hints210
def state211 : Known := next state210 step210
def hint211Block0 : List Nat := [515, 524, 513]
def hints211 : List Nat := hint211Block0
def step211 : Step := .del 869 hints211
def state212 : Known := next state211 step211
def hint212Block0 : List Nat := [334, 337, 340, 343, 833, 841, 867, 868, 869, 105]
def hint212Block1 : List Nat := [516, 525, 89, 101, 512]
def hints212 : List Nat := (hint212Block0 ++ hint212Block1)
def step212 : Step := .add 870 [(2, false), (80, true), (92, true)] hints212
def state213 : Known := next state212 step212
def hint213Block0 : List Nat := [334, 337, 340, 343, 833, 841, 867, 868, 869, 105]
def hint213Block1 : List Nat := [516, 525, 89, 101, 512]
def hints213 : List Nat := (hint213Block0 ++ hint213Block1)
def step213 : Step := .del 870 hints213
def state214 : Known := next state213 step213
def hint214Block0 : List Nat := [627, 636, 201, 213, 623]
def hints214 : List Nat := hint214Block0
def step214 : Step := .add 872 [(163, false), (152, true), (161, true)] hints214
def state215 : Known := next state214 step214
def hint215Block0 : List Nat := [872, 217, 626, 635, 201, 213, 624]
def hints215 : List Nat := hint215Block0
def step215 : Step := .add 873 [(152, true), (161, true), (164, true)] hints215
def state216 : Known := next state215 step215
def hint216Block0 : List Nat := [872]
def hints216 : List Nat := hint216Block0
def step216 : Step := .del 873 hints216
def state217 : Known := next state216 step216
def hint217Block0 : List Nat := [352, 355, 862]
def hints217 : List Nat := hint217Block0
def step217 : Step := .add 874 [(5, false), (152, false)] hints217
def state218 : Known := next state217 step217
def hint218Block0 : List Nat := [352, 355, 862]
def hints218 : List Nat := hint218Block0
def step218 : Step := .del 874 hints218
def state219 : Known := next state218 step218
def hint219Block0 : List Nat := [330, 5, 345, 25, 347]
def hints219 : List Nat := hint219Block0
def step219 : Step := .add 875 [(1, false), (5, true), (20, true)] hints219
def state220 : Known := next state219 step219
def hint220Block0 : List Nat := [345, 347]
def hints220 : List Nat := hint220Block0
def step220 : Step := .del 875 hints220
def state221 : Known := next state220 step220
def hint221Block0 : List Nat := [394, 397, 400, 403, 406, 409, 845, 850, 855, 870]
def hint221Block1 : List Nat := [418, 421, 865, 873, 874, 875, 1, 329, 344, 5]
def hint221Block2 : List Nat := [25, 348]
def hints221 : List Nat := (hint221Block0 ++ (hint221Block1 ++ hint221Block2))
def step221 : Step := .add 876 [(23, false), (161, true)] hints221
def state222 : Known := next state221 step221
def hint222Block0 : List Nat := [418, 421, 865, 873, 874]
def hints222 : List Nat := hint222Block0
def step222 : Step := .del 876 hints222
def state223 : Known := next state222 step222
def hint223Block0 : List Nat := [659, 237, 661, 670, 827]
def hints223 : List Nat := hint223Block0
def step223 : Step := .add 877 [(165, false), (23, true), (178, true)] hints223
def state224 : Known := next state223 step223
def hint224Block0 : List Nat := [467, 701, 61, 277, 466]
def hints224 : List Nat := hint224Block0
def step224 : Step := .add 878 [(219, false), (46, true), (208, true)] hints224
def state225 : Known := next state224 step224
def hint225Block0 : List Nat := [466]
def hints225 : List Nat := hint225Block0
def step225 : Step := .del 878 hints225
def state226 : Known := next state225 step225
def hint226Block0 : List Nat := [330, 348, 821, 29, 818, 877, 221, 658, 661, 237]
def hint226Block1 : List Nat := [668, 233, 411, 414, 672, 675, 820, 878, 819, 293]
def hint226Block2 : List Nat := [717, 289, 461, 698, 57, 273, 460]
def hints226 : List Nat := (hint226Block0 ++ (hint226Block1 ++ hint226Block2))
def step226 : Step := .add 879 [(4, false), (23, true), (178, true)] hints226
def state227 : Known := next state226 step226
def hint227Block0 : List Nat := [818, 877, 411, 414, 672, 675, 820, 878, 819, 717]
def hints227 : List Nat := hint227Block0
def step227 : Step := .del 879 hints227
def state228 : Known := next state227 step227
def hint228Block0 : List Nat := [477, 301, 480, 309, 724]
def hints228 : List Nat := hint228Block0
def step228 : Step := .add 880 [(52, false), (225, true), (231, true)] hints228
def state229 : Known := next state228 step228
def hint229Block0 : List Nat := [477, 480, 724]
def hints229 : List Nat := hint229Block0
def step229 : Step := .del 880 hints229
def state230 : Known := next state229 step229
def hint230Block0 : List Nat := [880, 69, 478, 481, 301, 309, 723]
def hints230 : List Nat := hint230Block0
def step230 : Step := .add 881 [(231, true), (51, true), (225, true)] hints230
def state231 : Known := next state230 step230
def hint231Block0 : List Nat := [880, 723]
def hints231 : List Nat := hint231Block0
def step231 : Step := .del 881 hints231
def state232 : Known := next state231 step231
def hint232Block0 : List Nat := [471, 297, 721, 305, 474]
def hints232 : List Nat := hint232Block0
def step232 : Step := .add 882 [(49, false), (222, true), (228, true)] hints232
def state233 : Known := next state232 step232
def hint233Block0 : List Nat := [471, 474]
def hints233 : List Nat := hint233Block0
def step233 : Step := .del 882 hints233
def state234 : Known := next state233 step233
def hint234Block0 : List Nat := [644, 647, 881, 725, 882, 65, 472, 475, 297, 305]
def hint234Block1 : List Nat := [720]
def hints234 : List Nat := (hint234Block0 ++ hint234Block1)
def step234 : Step := .add 883 [(162, false), (48, true), (51, true)] hints234
def state235 : Known := next state234 step234
def hint235Block0 : List Nat := [644, 647, 881, 725, 882, 720]
def hints235 : List Nat := hint235Block0
def step235 : Step := .del 883 hints235
def state236 : Known := next state235 step235
def hint236Block0 : List Nat := [484, 487, 205, 257, 630]
def hints236 : List Nat := hint236Block0
def step236 : Step := .add 885 [(56, false), (153, true), (192, true)] hints236
def state237 : Known := next state236 step236
def hint237Block0 : List Nat := [630]
def hints237 : List Nat := hint237Block0
def step237 : Step := .del 885 hints237
def state238 : Known := next state237 step237
def hint238Block0 : List Nat := [885, 73, 483, 205, 631, 257, 486]
def hints238 : List Nat := hint238Block0
def step238 : Step := .add 886 [(192, true), (54, true), (153, true)] hints238
def state239 : Known := next state238 step238
def hint239Block0 : List Nat := [885, 483, 486]
def hints239 : List Nat := hint239Block0
def step239 : Step := .del 886 hints239
def state240 : Known := next state239 step239
def hint240Block0 : List Nat := [489, 209, 634, 261, 492]
def hints240 : List Nat := hint240Block0
def step240 : Step := .add 887 [(58, false), (156, true), (195, true)] hints240
def state241 : Known := next state240 step240
def hint241Block0 : List Nat := [489, 492]
def hints241 : List Nat := hint241Block0
def step241 : Step := .del 887 hints241
def state242 : Known := next state241 step241
def hint242Block0 : List Nat := [617, 620, 886, 692, 887, 77, 490, 493, 209, 261]
def hint242Block1 : List Nat := [633]
def hints242 : List Nat := (hint242Block0 ++ hint242Block1)
def step242 : Step := .add 888 [(150, false), (54, true), (57, true)] hints242
def state243 : Known := next state242 step242
def hint243Block0 : List Nat := [617, 620, 886, 692, 887, 633]
def hints243 : List Nat := hint243Block0
def step243 : Step := .del 888 hints243
def state244 : Known := next state243 step243
def hint244Block0 : List Nat := [661, 670, 827]
def hints244 : List Nat := hint244Block0
def step244 : Step := .add 889 [(179, false), (4, true), (23, true)] hints244
def state245 : Known := next state244 step244
def hint245Block0 : List Nat := [681, 711, 285, 643, 876, 879, 889, 823, 237, 29]
def hint245Block1 : List Nat := [677, 392, 395, 398, 401, 404, 407, 416, 419, 313]
def hint245Block2 : List Nat := [797, 801, 782, 883, 706, 811, 281, 812, 638, 5]
def hint245Block3 : List Nat := [213, 350, 353, 624, 636, 888, 201, 217, 628]
def hints245 : List Nat := ((hint245Block0 ++ hint245Block1) ++ (hint245Block2 ++ hint245Block3))
def step245 : Step := .add 890 [(238, false), (211, true), (213, true), (235, true)] hints245
def state246 : Known := next state245 step245
def hint246Block0 : List Nat := [625, 637, 201, 217, 627]
def hints246 : List Nat := hint246Block0
def step246 : Step := .add 891 [(161, false), (150, true), (162, true)] hints246
def state247 : Known := next state246 step246
def hint247Block0 : List Nat := [627]
def hints247 : List Nat := hint247Block0
def step247 : Step := .del 891 hints247
def state248 : Known := next state247 step247
def hint248Block0 : List Nat := [816, 57, 460, 273, 699, 289, 463]
def hints248 : List Nat := hint248Block0
def step248 : Step := .add 892 [(216, true), (42, true), (204, true)] hints248
def state249 : Known := next state248 step248
def hint249Block0 : List Nat := [816, 460, 463]
def hints249 : List Nat := hint249Block0
def step249 : Step := .del 892 hints249
def state250 : Known := next state249 step249
def hint250Block0 : List Nat := [823, 29, 392, 395, 398, 401, 404, 407, 410, 413]
def hint250Block1 : List Nat := [416, 419, 797, 801, 782, 883, 811, 812, 5, 350]
def hint250Block2 : List Nat := [353, 824, 888, 891, 213, 638, 281, 706, 313, 677]
def hint250Block3 : List Nat := [237, 660, 669, 221, 658, 233, 671, 674, 892, 825]
def hint250Block4 : List Nat := [716, 293, 469, 703, 61, 277, 465]
def hints250 : List Nat := ((hint250Block0 ++ hint250Block1) ++ (hint250Block2 ++ (hint250Block3 ++ hint250Block4)))
def step250 : Step := .add 893 [(4, true), (23, true), (160, true), (179, true), (211, true), (235, true)] hints250
def state251 : Known := next state250 step250
def hint251Block0 : List Nat := [618, 621, 205, 209, 629, 632, 257, 261, 693]
def hints251 : List Nat := hint251Block0
def step251 : Step := .add 894 [(151, false), (155, true), (158, true), (194, true), (197, true)] hints251
def state252 : Known := next state251 step251
def hint252Block0 : List Nat := [858, 69, 478, 481, 301, 309, 722]
def hints252 : List Nat := hint252Block0
def step252 : Step := .add 895 [(232, true), (52, true), (226, true)] hints252
def state253 : Known := next state252 step252
def hint253Block0 : List Nat := [858, 69, 478, 481, 301, 309, 722]
def hints253 : List Nat := hint253Block0
def step253 : Step := .del 895 hints253
def state254 : Known := next state253 step253
def hint254Block0 : List Nat := [472, 297, 475, 305, 719]
def hints254 : List Nat := hint254Block0
def step254 : Step := .add 896 [(50, false), (223, true), (229, true)] hints254
def state255 : Known := next state254 step254
def hint255Block0 : List Nat := [472, 475, 719]
def hints255 : List Nat := hint255Block0
def step255 : Step := .del 896 hints255
def state256 : Known := next state255 step255
def hint256Block0 : List Nat := [645, 648, 895, 726, 896, 65, 470, 473, 297, 305]
def hint256Block1 : List Nat := [721]
def hints256 : List Nat := (hint256Block0 ++ hint256Block1)
def step256 : Step := .add 897 [(163, false), (49, true), (52, true)] hints256
def state257 : Known := next state256 step256
def hint257Block0 : List Nat := [645, 648, 895, 726, 896, 65, 470, 473, 297, 305]
def hint257Block1 : List Nat := [721]
def hints257 : List Nat := (hint257Block0 ++ hint257Block1)
def step257 : Step := .del 897 hints257
def state258 : Known := next state257 step257
def hint258Block0 : List Nat := [618, 205, 894, 490, 77, 491, 261, 693, 257, 629]
def hints258 : List Nat := hint258Block0
def step258 : Step := .add 898 [(197, true), (58, true), (151, false), (155, true), (194, true)] hints258
def state259 : Known := next state258 step258
def hint259Block0 : List Nat := [894, 629]
def hints259 : List Nat := hint259Block0
def step259 : Step := .del 898 hints259
def state260 : Known := next state259 step259
def hint260Block0 : List Nat := [493, 77, 634, 209, 488]
def hints260 : List Nat := hint260Block0
def step260 : Step := .add 899 [(197, false), (58, true), (157, true)] hints260
def state261 : Known := next state260 step260
def hint261Block0 : List Nat := [493, 634, 488]
def hints261 : List Nat := hint261Block0
def step261 : Step := .del 899 hints261
def state262 : Known := next state261 step261
def hint262Block0 : List Nat := [621, 899, 257, 898, 485, 73, 484]
def hints262 : List Nat := hint262Block0
def step262 : Step := .add 900 [(194, true), (55, true), (58, true), (151, false), (193, true)] hints262
def state263 : Known := next state262 step262
def hint263Block0 : List Nat := [257, 898, 485, 484]
def hints263 : List Nat := hint263Block0
def step263 : Step := .del 900 hints263
def state264 : Known := next state263 step263
def hint264Block0 : List Nat := [487, 631, 73, 205, 482]
def hints264 : List Nat := hint264Block0
def step264 : Step := .add 901 [(194, false), (55, true), (154, true)] hints264
def state265 : Known := next state264 step264
def hint265Block0 : List Nat := [487, 631, 73, 205, 482]
def hints265 : List Nat := hint265Block0
def step265 : Step := .del 901 hints265
def state266 : Known := next state265 step265
def hint266Block0 : List Nat := [618, 621, 901, 899, 900, 693, 261, 491, 632, 77]
def hint266Block1 : List Nat := [209, 490]
def hints266 : List Nat := (hint266Block0 ++ hint266Block1)
def step266 : Step := .add 902 [(151, false), (55, true), (58, true)] hints266
def state267 : Known := next state266 step266
def hint267Block0 : List Nat := [618, 621, 901, 899, 900, 693, 261, 491, 632, 77]
def hint267Block1 : List Nat := [209, 490]
def hints267 : List Nat := (hint267Block0 ++ hint267Block1)
def step267 : Step := .del 902 hints267
def state268 : Known := next state267 step267
def hint268Block0 : List Nat := [623, 213, 626, 217, 637]
def hints268 : List Nat := hint268Block0
def step268 : Step := .add 903 [(150, false), (160, true), (163, true)] hints268
def state269 : Known := next state268 step268
def hint269Block0 : List Nat := [623, 626, 637]
def hints269 : List Nat := hint269Block0
def step269 : Step := .del 903 hints269
def state270 : Known := next state269 step269
def hint270Block0 : List Nat := [893, 330, 348, 351, 354, 821, 902, 29, 417, 420]
def hint270Block1 : List Nat := [897, 903, 201, 625, 628, 213, 217, 635]
def hints270 : List Nat := (hint270Block0 ++ hint270Block1)
def step270 : Step := .add 904 [(23, true), (160, true), (179, true), (211, true), (235, true)] hints270
def state271 : Known := next state270 step270
def hint271Block0 : List Nat := [893]
def hints271 : List Nat := hint271Block0
def step271 : Step := .del 904 hints271
def state272 : Known := next state271 step271
def hint272Block0 : List Nat := [495, 81, 663, 265, 497]
def hints272 : List Nat := hint272Block0
def step272 : Step := .add 906 [(169, false), (62, true), (200, true)] hints272
def state273 : Known := next state272 step272
def hint273Block0 : List Nat := [495, 663, 497]
def hints273 : List Nat := hint273Block0
def step273 : Step := .del 906 hints273
def state274 : Known := next state273 step273
def hint274Block0 : List Nat := [906, 225, 494, 662, 81, 265, 498]
def hints274 : List Nat := hint274Block0
def step274 : Step := .add 907 [(200, true), (62, true), (170, true)] hints274
def state275 : Known := next state274 step274
def hint275Block0 : List Nat := [906, 225, 494, 662, 81, 265, 498]
def hints275 : List Nat := hint275Block0
def step275 : Step := .del 907 hints275
def state276 : Known := next state275 step275
def hint276Block0 : List Nat := [501, 85, 666, 269, 503]
def hints276 : List Nat := hint276Block0
def step276 : Step := .add 908 [(172, false), (65, true), (203, true)] hints276
def state277 : Known := next state276 step276
def hint277Block0 : List Nat := [501, 666, 503]
def hints277 : List Nat := hint277Block0
def step277 : Step := .del 908 hints277
def state278 : Known := next state277 step277
def hint278Block0 : List Nat := [652, 655, 907, 697, 908, 229, 500, 665, 85, 269]
def hint278Block1 : List Nat := [504]
def hints278 : List Nat := (hint278Block0 ++ hint278Block1)
def step278 : Step := .add 909 [(167, false), (62, true), (65, true)] hints278
def state279 : Known := next state278 step278
def hint279Block0 : List Nat := [652, 655, 907, 697, 908, 229, 500, 665, 85, 269]
def hint279Block1 : List Nat := [504]
def hints279 : List Nat := (hint279Block0 ++ hint279Block1)
def step279 : Step := .del 909 hints279
def state280 : Known := next state279 step279
def hint280Block0 : List Nat := [461, 57, 698, 273, 459]
def hints280 : List Nat := hint280Block0
def step280 : Step := .add 910 [(216, false), (44, true), (206, true)] hints280
def state281 : Known := next state280 step280
def hint281Block0 : List Nat := [461, 698, 459]
def hints281 : List Nat := hint281Block0
def step281 : Step := .del 910 hints281
def state282 : Known := next state281 step281
def hint282Block0 : List Nat := [467, 61, 465, 277, 701]
def hints282 : List Nat := hint282Block0
def step282 : Step := .add 911 [(219, false), (47, true), (209, true)] hints282
def state283 : Known := next state282 step282
def hint283Block0 : List Nat := [467, 701]
def hints283 : List Nat := hint283Block0
def step283 : Step := .del 911 hints283
def state284 : Known := next state283 step283
def hint284Block0 : List Nat := [462, 699, 57, 273, 458]
def hints284 : List Nat := hint284Block0
def step284 : Step := .add 912 [(217, false), (44, true), (206, true)] hints284
def state285 : Known := next state284 step284
def hint285Block0 : List Nat := [462, 699, 57, 273, 458]
def hints285 : List Nat := hint285Block0
def step285 : Step := .del 912 hints285
def state286 : Known := next state285 step285
def hint286Block0 : List Nat := [673, 676, 912, 910, 911, 289, 718, 293, 468, 61]
def hint286Block1 : List Nat := [702, 277, 464]
def hints286 : List Nat := (hint286Block0 ++ hint286Block1)
def step286 : Step := .add 913 [(176, false), (44, true), (47, true)] hints286
def state287 : Known := next state286 step286
def hint287Block0 : List Nat := [673, 676, 912, 910, 911, 289, 718, 468, 702, 464]
def hints287 : List Nat := hint287Block0
def step287 : Step := .del 913 hints287
def state288 : Known := next state287 step287
def hint288Block0 : List Nat := [875, 1, 329, 5, 348, 344, 25]
def hints288 : List Nat := hint288Block0
def step288 : Step := .add 914 [(5, true), (2, true), (20, true)] hints288
def state289 : Known := next state288 step288
def hint289Block0 : List Nat := [875, 1, 329, 344, 25]
def hints289 : List Nat := hint289Block0
def step289 : Step := .del 914 hints289
def state290 : Known := next state289 step289
def hint290Block0 : List Nat := [669, 237, 659, 221, 657]
def hints290 : List Nat := hint290Block0
def step290 : Step := .add 915 [(175, false), (167, true), (179, true)] hints290
def state291 : Known := next state290 step290
def hint291Block0 : List Nat := [657]
def hints291 : List Nat := hint291Block0
def step291 : Step := .del 915 hints291
def state292 : Known := next state291 step291
def hint292Block0 : List Nat := [708, 729, 890, 317, 682, 712, 285, 642, 904, 394]
def hint292Block1 : List Nat := [397, 400, 403, 406, 409, 412, 415, 845, 850, 855]
def hint292Block2 : List Nat := [913, 870, 914, 358, 361, 909, 915, 233, 656, 668]
def hint292Block3 : List Nat := [221, 237, 660]
def hints292 : List Nat := ((hint292Block0 ++ hint292Block1) ++ (hint292Block2 ++ hint292Block3))
def step292 : Step := .add 916 [(241, false), (213, true), (237, true)] hints292
def state293 : Known := next state292 step292
def hint293Block0 : List Nat := [890, 904]
def hints293 : List Nat := hint293Block0
def step293 : Step := .del 916 hints293
def state294 : Known := next state293 step293
def hint294Block0 : List Nat := [656, 221, 660, 237, 668]
def hints294 : List Nat := hint294Block0
def step294 : Step := .add 917 [(174, false), (167, true), (179, true)] hints294
def state295 : Known := next state294 step294
def hint295Block0 : List Nat := [656, 668]
def hints295 : List Nat := hint295Block0
def step295 : Step := .del 917 hints295
def state296 : Known := next state295 step295
def hint296Block0 : List Nat := [660, 237, 879, 677, 823, 313, 29, 705, 392, 395]
def hint296Block1 : List Nat := [398, 401, 404, 407, 416, 419, 281, 797, 801, 782]
def hint296Block2 : List Nat := [883, 638, 811, 812, 5, 350, 353, 888, 891, 213]
def hint296Block3 : List Nat := [624, 636, 201, 217, 628]
def hints296 : List Nat := ((hint296Block0 ++ hint296Block1) ++ (hint296Block2 ++ hint296Block3))
def step296 : Step := .add 918 [(166, false), (23, true), (179, true), (212, true), (236, true)] hints296
def state297 : Known := next state296 step296
def hint297Block0 : List Nat := [330, 348, 351, 354, 821, 29, 902, 417, 420, 897]
def hint297Block1 : List Nat := [903, 201, 628, 217, 625, 213, 635]
def hints297 : List Nat := (hint297Block0 ++ hint297Block1)
def step297 : Step := .add 919 [(4, false), (23, true), (160, true)] hints297
def state298 : Known := next state297 step297
def hint298Block0 : List Nat := [330, 348, 351, 354, 821, 902, 417, 420, 897, 903]
def hint298Block1 : List Nat := [625, 635]
def hints298 : List Nat := (hint298Block0 ++ hint298Block1)
def step298 : Step := .del 919 hints298
def state299 : Known := next state298 step298
def hint299Block0 : List Nat := [915, 917, 233, 913, 415, 918, 221, 659, 824, 237]
def hint299Block1 : List Nat := [678, 313, 704, 281, 639, 919, 823, 5, 29, 392]
def hint299Block2 : List Nat := [395, 398, 401, 404, 407, 797, 801, 782, 811, 812]
def hints299 : List Nat := (hint299Block0 ++ (hint299Block1 ++ hint299Block2))
def step299 : Step := .add 920 [(179, true), (44, true), (167, true), (212, true), (236, true)] hints299
def state300 : Known := next state299 step299
def hint300Block0 : List Nat := [920, 670, 682, 827, 317, 876, 711, 643, 285]
def hints300 : List Nat := hint300Block0
def step300 : Step := .add 921 [(167, true), (44, true), (212, true), (213, true), (236, true), (237, true)] hints300
def state301 : Known := next state300 step300
def hint301Block0 : List Nat := [920]
def hints301 : List Nat := hint301Block0
def step301 : Step := .del 921 hints301
def state302 : Known := next state301 step301
def hint302Block0 : List Nat := [358, 361, 909]
def hints302 : List Nat := hint302Block0
def step302 : Step := .add 922 [(5, false), (167, false)] hints302
def state303 : Known := next state302 step302
def hint303Block0 : List Nat := [358, 361, 909]
def hints303 : List Nat := hint303Block0
def step303 : Step := .del 922 hints303
def state304 : Known := next state303 step303
def hint304Block0 : List Nat := [394, 397, 400, 403, 406, 409, 845, 850, 855, 870]
def hint304Block1 : List Nat := [914]
def hints304 : List Nat := (hint304Block0 ++ hint304Block1)
def step304 : Step := .add 923 [(23, false), (5, true)] hints304
def state305 : Known := next state304 step304
def hint305Block0 : List Nat := [394, 397, 400, 403, 406, 409, 845, 850, 855, 870]
def hint305Block1 : List Nat := [914]
def hints305 : List Nat := (hint305Block0 ++ hint305Block1)
def step305 : Step := .del 923 hints305
def state306 : Known := next state305 step305
def hint306Block0 : List Nat := [923, 216, 919, 823, 5, 29, 350, 353, 416, 419]
def hint306Block1 : List Nat := [888, 883, 891]
def hints306 : List Nat := (hint306Block0 ++ hint306Block1)
def step306 : Step := .add 924 [(161, false), (5, true)] hints306
def state307 : Known := next state306 step306
def hint307Block0 : List Nat := [216, 891]
def hints307 : List Nat := hint307Block0
def step307 : Step := .del 924 hints307
def state308 : Known := next state307 step307
def hint308Block0 : List Nat := [671, 674, 892, 825, 716, 293, 469, 703, 61, 277]
def hint308Block1 : List Nat := [465]
def hints308 : List Nat := (hint308Block0 ++ hint308Block1)
def step308 : Step := .add 925 [(174, false), (42, true), (45, true)] hints308
def state309 : Known := next state308 step308
def hint309Block0 : List Nat := [671, 674, 892, 825, 716, 293, 469, 703, 61, 277]
def hint309Block1 : List Nat := [465]
def hints309 : List Nat := (hint309Block0 ++ hint309Block1)
def step309 : Step := .del 925 hints309
def state310 : Known := next state309 step309
def hint310Block0 : List Nat := [823, 5, 924, 923, 29, 350, 353, 410, 413, 416]
def hint310Block1 : List Nat := [419, 888, 925, 883, 233, 669, 237, 677, 313, 705]
def hint310Block2 : List Nat := [281, 638, 213, 624, 636, 201, 217, 628]
def hints310 : List Nat := (hint310Block0 ++ (hint310Block1 ++ hint310Block2))
def step310 : Step := .add 926 [(4, true), (5, true), (176, true), (179, true), (212, true), (236, true)] hints310
def state311 : Known := next state310 step310
def hint311Block0 : List Nat := [677, 638]
def hints311 : List Nat := hint311Block0
def step311 : Step := .del 926 hints311
def state312 : Known := next state311 step311
def hint312Block0 : List Nat := [658, 922, 923, 661, 926, 919, 879, 639, 678, 281]
def hint312Block1 : List Nat := [313, 704]
def hints312 : List Nat := (hint312Block0 ++ hint312Block1)
def step312 : Step := .add 927 [(167, false), (212, true), (236, true)] hints312
def state313 : Known := next state312 step312
def hint313Block0 : List Nat := [661, 926]
def hints313 : List Nat := hint313Block0
def step313 : Step := .del 927 hints313
def state314 : Known := next state313 step313
def hint314Block0 : List Nat := [734, 731, 713, 916, 321, 709, 730, 927, 921, 412]
def hint314Block1 : List Nat := [827, 670, 918, 221, 824, 659, 237, 678, 313, 704]
def hint314Block2 : List Nat := [281, 639, 919, 823, 5, 29, 392, 395, 398, 401]
def hint314Block3 : List Nat := [404, 407, 797, 801, 782, 811, 812]
def hints314 : List Nat := ((hint314Block0 ++ hint314Block1) ++ (hint314Block2 ++ hint314Block3))
def step314 : Step := .add 928 [(243, false)] hints314
def state315 : Known := next state314 step314
def hint315Block0 : List Nat := [734, 731, 713, 916, 927, 921, 827, 670, 918, 659]
def hints315 : List Nat := hint315Block0
def step315 : Step := .del 928 hints315
def state316 : Known := next state315 step315
def hint316Block0 : List Nat := [8, 823, 29, 392, 395, 398, 401, 404, 407, 797]
def hint316Block1 : List Nat := [801, 782, 811, 812]
def hints316 : List Nat := (hint316Block0 ++ hint316Block1)
def step316 : Step := .add 929 [(5, false), (23, true)] hints316
def state317 : Known := next state316 step316
def hint317Block0 : List Nat := [8, 392, 395, 398, 401, 404, 407, 797, 801, 782]
def hint317Block1 : List Nat := [811, 812]
def hints317 : List Nat := (hint317Block0 ++ hint317Block1)
def step317 : Step := .del 929 hints317
def state318 : Known := next state317 step317
def hint318Block0 : List Nat := [660, 669, 233, 221, 658]
def hints318 : List Nat := hint318Block0
def step318 : Step := .add 930 [(178, false), (165, true), (174, true)] hints318
def state319 : Known := next state318 step318
def hint319Block0 : List Nat := [660, 669, 221, 658]
def hints319 : List Nat := hint319Block0
def step319 : Step := .del 930 hints319
def state320 : Known := next state319 step319
def hint320Block0 : List Nat := [928, 714, 325, 733, 317, 711]
def hints320 : List Nat := hint320Block0
def step320 : Step := .add 931 [(214, false), (237, true)] hints320
def state321 : Known := next state320 step320
def hint321Block0 : List Nat := [711]
def hints321 : List Nat := hint321Block0
def step321 : Step := .del 931 hints321
def state322 : Known := next state321 step321
def hint322Block0 : List Nat := [928, 715, 325, 732, 317, 712]
def hints322 : List Nat := hint322Block0
def step322 : Step := .add 932 [(215, false), (237, true)] hints322
def state323 : Known := next state322 step322
def hint323Block0 : List Nat := [712]
def hints323 : List Nat := hint323Block0
def step323 : Step := .del 932 hints323
def state324 : Known := next state323 step323
def hint324Block0 : List Nat := [889, 823, 929, 29, 924, 5, 410, 413, 416, 419]
def hint324Block1 : List Nat := [350, 353, 824, 925, 883, 888, 930, 237, 680, 932]
def hint324Block2 : List Nat := [931, 285, 641, 213, 624, 636, 201, 217, 628]
def hints324 : List Nat := (hint324Block0 ++ (hint324Block1 ++ hint324Block2))
def step324 : Step := .add 933 [(4, true), (23, true)] hints324
def state325 : Known := next state324 step324
def hint325Block0 : List Nat := [889, 823, 929, 29, 924, 5, 410, 413, 416, 419]
def hint325Block1 : List Nat := [350, 353, 824, 925, 883, 888, 930, 237, 680, 932]
def hint325Block2 : List Nat := [931, 641, 213, 624, 636, 201, 217, 628]
def hints325 : List Nat := (hint325Block0 ++ (hint325Block1 ++ hint325Block2))
def step325 : Step := .del 933 hints325
def state326 : Known := next state325 step325
def hint326Block0 : List Nat := [706, 281, 707, 321, 730]
def hints326 : List Nat := hint326Block0
def step326 : Step := .add 934 [(236, false), (211, true), (241, true)] hints326
def state327 : Known := next state326 step326
def hint327Block0 : List Nat := [706, 730]
def hints327 : List Nat := hint327Block0
def step327 : Step := .del 934 hints327
def state328 : Known := next state327 step327
def hint328Block0 : List Nat := [934, 313, 704, 728, 281, 321, 709]
def hints328 : List Nat := hint328Block0
def step328 : Step := .add 935 [(241, true), (211, true), (235, true)] hints328
def state329 : Known := next state328 step328
def hint329Block0 : List Nat := [934, 709]
def hints329 : List Nat := hint329Block0
def step329 : Step := .del 935 hints329
def state330 : Known := next state329 step329
def hint330Block0 : List Nat := [928, 933, 919, 879, 639, 642, 678, 681, 935, 735]
def hint330Block1 : List Nat := [325, 715, 285, 710, 317, 733]
def hints330 : List Nat := (hint330Block0 ++ hint330Block1)
def step330 : Step := .add 936 [(23, true)] hints330
def state331 : Known := next state330 step330
def hint331Block0 : List Nat := [933, 919, 879, 639, 642, 678, 681, 935, 735, 715]
def hint331Block1 : List Nat := [733]
def hints331 : List Nat := (hint331Block0 ++ hint331Block1)
def step331 : Step := .del 936 hints331
def state332 : Known := next state331 step331
def hint332Block0 : List Nat := [936, 412, 415, 923, 913, 922, 915, 917, 233]
def hints332 : List Nat := hint332Block0
def step332 : Step := .add 937 [(179, true)] hints332
def state333 : Known := next state332 step332
def hint333Block0 : List Nat := [412, 415, 923, 913, 922, 915, 917, 233]
def hints333 : List Nat := hint333Block0
def step333 : Step := .del 937 hints333
def state334 : Known := next state333 step333
def hint334Block0 : List Nat := [936, 876, 643, 937, 682, 714, 732, 285, 317, 710]
def hints334 : List Nat := hint334Block0
def step334 : Step := .add 938 [(244, false)] hints334
def state335 : Known := next state334 step334
def hint335Block0 : List Nat := [643, 682, 714, 732, 285, 317, 710]
def hints335 : List Nat := hint335Block0
def step335 : Step := .del 938 hints335
def state336 : Known := next state335 step335
def hint336Block0 : List Nat := [928, 937, 679, 938, 325, 736, 704, 313, 707, 321]
def hint336Block1 : List Nat := [729]
def hints336 : List Nat := (hint336Block0 ++ hint336Block1)
def step336 : Step := .add 939 [(210, false)] hints336
def state337 : Known := next state336 step336
def hint337Block0 : List Nat := [704, 707, 729]
def hints337 : List Nat := hint337Block0
def step337 : Step := .del 939 hints337
def state338 : Known := next state337 step337
def hint338Block0 : List Nat := [928, 936, 876, 640, 937, 679, 938, 325, 736, 939]
def hint338Block1 : List Nat := [281, 705, 708, 313, 321, 728]
def hints338 : List Nat := (hint338Block0 ++ hint338Block1)
def step338 : Step := .add 941 [] hints338
def state339 : Known := next state338 step338
def chunk0 : List Step := [step0, step1, step2, step3, step4, step5, step6]
def chunk1 : List Step := [step7, step8, step9, step10, step11, step12, step13]
def chunk2 : List Step := [step14, step15, step16, step17, step18, step19, step20]
def chunk3 : List Step := [step21, step22, step23, step24, step25, step26, step27]
def chunk4 : List Step := [step28, step29, step30, step31, step32, step33, step34, step35, step36, step37]
def chunk5 : List Step := [step38, step39, step40, step41, step42, step43, step44]
def chunk6 : List Step := [step45, step46, step47, step48, step49, step50, step51]
def chunk7 : List Step := [step52, step53, step54, step55, step56, step57, step58]
def chunk8 : List Step := [step59, step60, step61, step62, step63, step64, step65, step66, step67, step68]
def chunk9 : List Step := [step69, step70, step71, step72, step73, step74, step75, step76, step77, step78]
def chunk10 : List Step := [step79, step80, step81, step82, step83, step84, step85, step86, step87]
def chunk11 : List Step := [step88, step89, step90, step91, step92, step93, step94, step95, step96, step97]
def chunk12 : List Step := [step98, step99, step100, step101, step102, step103, step104, step105, step106, step107]
def chunk13 : List Step := [step108, step109, step110, step111, step112, step113, step114, step115, step116, step117]
def chunk14 : List Step := [step118, step119, step120, step121, step122, step123, step124, step125]
def chunk15 : List Step := [step126, step127, step128, step129, step130, step131, step132, step133]
def chunk16 : List Step := [step134, step135, step136, step137, step138, step139, step140, step141]
def chunk17 : List Step := [step142, step143, step144, step145, step146, step147, step148, step149, step150]
def chunk18 : List Step := [step151, step152, step153, step154, step155, step156, step157, step158, step159, step160]
def chunk19 : List Step := [step161, step162, step163, step164, step165, step166, step167, step168, step169]
def chunk20 : List Step := [step170, step171, step172, step173, step174, step175, step176, step177, step178, step179]
def chunk21 : List Step := [step180, step181, step182, step183, step184, step185, step186, step187, step188, step189]
def chunk22 : List Step := [step190, step191, step192, step193, step194, step195]
def chunk23 : List Step := [step196, step197, step198, step199, step200, step201, step202, step203, step204]
def chunk24 : List Step := [step205, step206, step207, step208, step209, step210, step211, step212, step213, step214]
def chunk25 : List Step := [step215, step216, step217, step218, step219, step220, step221, step222, step223]
def chunk26 : List Step := [step224, step225, step226, step227, step228, step229, step230, step231, step232]
def chunk27 : List Step := [step233, step234, step235, step236, step237, step238, step239, step240, step241, step242]
def chunk28 : List Step := [step243, step244, step245, step246, step247, step248, step249, step250]
def chunk29 : List Step := [step251, step252, step253, step254, step255, step256, step257, step258]
def chunk30 : List Step := [step259, step260, step261, step262, step263, step264, step265, step266, step267, step268]
def chunk31 : List Step := [step269, step270, step271, step272, step273, step274, step275, step276, step277, step278]
def chunk32 : List Step := [step279, step280, step281, step282, step283, step284, step285, step286, step287, step288]
def chunk33 : List Step := [step289, step290, step291, step292, step293, step294, step295, step296, step297]
def chunk34 : List Step := [step298, step299, step300, step301, step302, step303, step304, step305, step306]
def chunk35 : List Step := [step307, step308, step309, step310, step311, step312, step313, step314, step315, step316]
def chunk36 : List Step := [step317, step318, step319, step320, step321, step322, step323, step324, step325, step326]
def chunk37 : List Step := [step327, step328, step329, step330, step331, step332, step333, step334, step335, step336]
def chunk38 : List Step := [step337, step338]
def proof : List Step := (((((chunk0 ++ chunk1) ++ (chunk2 ++ chunk3)) ++ ((chunk4 ++ chunk5) ++ (chunk6 ++ (chunk7 ++ chunk8)))) ++ (((chunk9 ++ chunk10) ++ (chunk11 ++ (chunk12 ++ chunk13))) ++ ((chunk14 ++ chunk15) ++ (chunk16 ++ (chunk17 ++ chunk18))))) ++ ((((chunk19 ++ chunk20) ++ (chunk21 ++ (chunk22 ++ chunk23))) ++ ((chunk24 ++ chunk25) ++ (chunk26 ++ (chunk27 ++ chunk28)))) ++ (((chunk29 ++ chunk30) ++ (chunk31 ++ (chunk32 ++ chunk33))) ++ ((chunk34 ++ chunk35) ++ (chunk36 ++ (chunk37 ++ chunk38))))))

end LocalRup.SymmetryFree

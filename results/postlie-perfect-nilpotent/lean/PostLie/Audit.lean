import PostLie.Statement

/-! Both endpoint theorems rest on Lean's three standard axioms and the two cited
textbook theorems in `PostLie/Textbook.lean`; the build fails otherwise. -/

/--
info: 'PostLie.solvable_of_trace_right_eq_zero' depends on axioms: [propext,
 Classical.choice,
 PostLie.levi_nonzero_semisimple,
 PostLie.whitehead_first,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PostLie.solvable_of_trace_right_eq_zero

/--
info: 'PostLie.no_product_of_perfect' depends on axioms: [propext,
 Classical.choice,
 PostLie.levi_nonzero_semisimple,
 PostLie.whitehead_first,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms PostLie.no_product_of_perfect

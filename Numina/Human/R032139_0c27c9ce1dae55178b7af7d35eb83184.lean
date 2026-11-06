import Mathlib

/- Trae is searching for a treasure on the beach. From point $A$, he is told to walk two meters north, three meters east, and then two meters north to point $B$. In meters, what is the length of $\overline{AB}$? -/
theorem algebra_21329 (A B : ℝ × ℝ)
    (hA : A = (0, 0)) (hB : B = (3, 4)) :
    Real.sqrt ((B.1 - A.1)^2 + (B.2 - A.2)^2) = 5 := by
  simp only [hB, hA, Prod.mk_zero_zero, Prod.fst_zero, sub_zero, Prod.snd_zero]
  refine (Real.sqrt_eq_iff_mul_self_eq_of_pos (by linarith)).mpr ?_
  ring
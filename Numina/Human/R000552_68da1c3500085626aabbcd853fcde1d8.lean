import Mathlib

/-Points $A$ and $B$ are on parabola $y=4x^2+7x-1$, and the origin is the midpoint of $\overline{AB}$. Find the square of the length of $\overline{AB}$.-/
theorem algebra_12350 {A B : ℝ × ℝ} (hA : A.2 = 4 * A.1 ^ 2 + 7 * A.1 - 1)
(hB : B.2 = 4 * B.1 ^ 2 + 7 * B.1 - 1) (mid1 : (A.1 + B.1) / 2 = 0) 
(mid2 : (A.2 + B.2) / 2 = 0): (A.1 - B.1) ^ 2 + (A.2 - B.2) ^ 2 = 50 := by
-- Simplify assumptions
  simp at mid1 mid2
  rw [add_eq_zero_iff_eq_neg] at mid1
-- Solve for $A.1$
  apply_fun (fun x => x + B.2) at hA; nth_rw 2 [hB] at hA
  rw [mid2, mid1] at hA; ring_nf at hA; symm at hA
  rw [neg_add_eq_zero] at hA; symm at hA
  apply_fun (fun x => x / 8) at hA; ring_nf at hA
  rw [show (1:ℝ)/4= (1/2)^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at hA
-- Solve for the rest of the variables and finish the final goal
  rcases hA with hA|hA
  · simp_all; ring_nf at *
    rw [add_eq_zero_iff_neg_eq] at mid2
    rw [← mid2]; ring
  simp_all; ring_nf at *
  rw [neg_div, neg_add_eq_zero] at mid2
  rw [← mid2]; ring
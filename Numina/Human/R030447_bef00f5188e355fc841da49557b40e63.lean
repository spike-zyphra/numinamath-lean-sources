import Mathlib
open Real

/- There are two positive numbers that may be inserted between 3 and 9 such that
the first three are in geometric progression
while the last three are in arithmetic progression. The sum of those two positive
numbers is
(A) 13+1/2 (B) 11+1/4 (C) 10+1/2 (D) 10 (E) 9+1/2 -/
theorem algebra_96840 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
(h1 : b-a=9-b) (h2 : b/a=a/3) : a + b = 11 + 1 / 4 := by
  -- eliminate b
  have h1':b=(9+a)/2 := by field_simp; linarith
  rw [h1'] at h2;field_simp at h2
  have hq: 2*(a*a)+(-3)*a+(-27)=0 := by linarith
  -- solve the quadratic equation of a to get the answer
  rw [quadratic_eq_zero_iff (by simp) (by unfold discrim; norm_num : discrim (2:ℝ) (-3) (-27) = 15 * 15)] at hq
  norm_num at hq
  cases hq <;> linarith
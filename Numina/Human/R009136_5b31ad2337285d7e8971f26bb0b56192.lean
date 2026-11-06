import Mathlib

/- The length of the longer side of rectangle $R$ is $10$ percent more than the length of a side of square $S.$ The length of the shorter side of rectangle $R$ is $10$ percent less than the length of a side of square $S.$ What is the ratio of the area of rectangle $R$ to the area of square $S?$ Express your answer as a common fraction. -/
theorem algebra_12955 {s l a : ℝ}
    (hpos : 0 < l ∧ 0 < s ∧ 0 < a)
    (h0 : s < l)
    (h1 : (l - a) = 0.1 * a)
    (h2 : (a - s) = 0.1 * a) :
    s * l / a ^ 2 = 99 / 100 := by
  have : l = (1 + 0.1) * a := by linarith only [h1]
  have : s = (1 - 0.1) * a := by linarith only [h2]
  simp_all
  ring_nf
  rw [inv_pow, mul_inv_cancel₀, one_mul]
  apply ne_of_gt
  refine Real.lt_sq_of_sqrt_lt ?_
  simp [hpos]
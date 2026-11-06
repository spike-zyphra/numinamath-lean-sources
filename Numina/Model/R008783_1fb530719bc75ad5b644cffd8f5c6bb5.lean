import Mathlib

theorem algebra_15793 (t : ℝ) (ht : t > 0) (h : -6 * t ^ 2 - 10 * t + 56 = 0) :
    round (t * 100) / 100 = (2.33 : ℝ) := by
  have h1 : -6 * t ^ 2 - 10 * t + 56 = 0 := h
  -- convert to $6t^2 +10t -56 =0$
  have h2 : 6 * t ^ 2 + 10 * t - 56 = 0 := by
    nlinarith 
  -- factor the equation
  have h4 : 3 * t^2 + 5 * t - 28 = 0 := by
    nlinarith 
  have h5 : (3 * t - 7) * (t + 4) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case where $3t - 7 = 0$:
    have ht1 : t = 7 / 3 := by
      linarith 
    rw [ht1]
    rw [round_eq]
    norm_num
    <;> try { norm_num }
    <;> try { linarith }
  · -- Case where $t + 4 = 0$:
    have ht2 : t = -4 := by
      linarith 
    linarith -- contradiction with t > 0
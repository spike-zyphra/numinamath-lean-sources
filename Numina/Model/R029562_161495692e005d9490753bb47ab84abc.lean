import Mathlib

open Real Set

theorem algebra_282739 :
    IsGreatest {z : ℝ | ∃ x y, z = (2 * x + sqrt 2 * y) / (2 * x ^ 4 + 4 * y ^ 4 + 9)} (1 / 4) := by
  constructor
  · -- Show that 1/4 is in the set
    use 1, 1 / Real.sqrt 2
    have h1 : sqrt 2 ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      all_goals linarith
    have h2 : sqrt 2 ^ 4 = 4 := by
      calc
        sqrt 2 ^ 4 = (sqrt 2 ^ 2) ^ 2 := by ring
        _ = 2 ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        _ = 4 := by norm_num
    have h3 : sqrt 2 * (1 / sqrt 2) = 1 := by
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
    rw [h3]
    norm_num [h2]
    <;> try { nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)] }
  · -- Show that 1/4 is the greatest value in the set
    intro z hz
    rcases hz with ⟨x, y, hz⟩
    have h4 : (2 * x + sqrt 2 * y) / (2 * x ^ 4 + 4 * y ^ 4 + 9) ≤ 1 / 4 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg (x - 1), sq_nonneg (y - 1 / sqrt 2), 
        sq_nonneg (sqrt 2 * y - 1), sq_nonneg (x * sqrt 2 - 1 * 1), sq_nonneg (x * sqrt 2 - 2 * y), sq_nonneg (x ^ 2 * sqrt 2 -1 * y),
        Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [hz, h4]
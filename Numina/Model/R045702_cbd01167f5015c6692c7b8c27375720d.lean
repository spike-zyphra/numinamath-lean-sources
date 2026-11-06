import Mathlib

theorem algebra_20614 {x : ℕ} : (66 - 2 ^ x : ℝ) / (2 ^ x + 3) = (4 - 2 ^ x) / (2 ^ (x + 1) + 6) → x = 7 := by 
  intro h
  have h1 : (2 : ℝ) ^ x > 0 := by
    have h2 : (2 : ℝ) > 0 := by norm_num
    apply pow_pos
    all_goals linarith
  have h2d1 : (2 ^ x + 3 : ℝ) ≠ 0 := by
    linarith [h1]
  have h2d2 : (2 ^ (x + 1) + 6 : ℝ) ≠ 0 := by 
    have h3 : (2 : ℝ) ^ (x + 1) > 0 := by 
      have h2 : (2 : ℝ) > 0 := by norm_num
      apply pow_pos
      all_goals linarith
    linarith [h3]
  have eq1 : (66 - (2 : ℝ) ^ x) / ((2 : ℝ) ^ x + 3) = (4 - (2 : ℝ) ^ x) / ((2 : ℝ) ^ (x + 1) + 6) := h 
  have eq2 : (66 - (2 : ℝ) ^ x) * ((2 : ℝ) ^ (x + 1) + 6) = (4 - (2 : ℝ) ^ x) * ((2 : ℝ) ^ x + 3) := by 
    field_simp [h2d1, h2d2] at eq1 ⊢
    nlinarith
  have eq3 : ((2 : ℝ) ^ x) ^ 2 - 125 * ((2 : ℝ) ^ x) - 384 = 0 := by 
    have h4 : (2 : ℝ) ^ (x + 1) = 2 * (2 : ℝ) ^ x := by 
      ring_nf
    rw [h4] at eq2 
    nlinarith [sq_nonneg ((2 : ℝ) ^ x - 128), sq_nonneg ((2 : ℝ) ^ x + 3), sq_nonneg ((2 : ℝ) ^ x - 16)]
  have eq4 : ((2 : ℝ) ^ x - 128) * ((2 : ℝ) ^ x + 3) = 0 := by
    nlinarith [eq3]
  cases' (mul_eq_zero.1 eq4) with h6 h7 
  · -- First case, (2 : ℝ) ^ x - 128 = 0
    have eq6 : (2 : ℝ) ^ x = 128 := by linarith
    have eq7 : x = 7 := by 
      have h3 : (2 : ℝ) ^ x = 128 := eq6 
      have h4 : (2 : ℝ) ^ (7 : ℕ) = (128 : ℝ) := by norm_num 
      have h5 : (2 : ℝ) ^ x = (2 : ℝ) ^ (7 : ℕ) := by 
        rw [h3, h4] 
      exact Nat.cast_injective ((by simpa using h5))
    linarith 
  · -- Second case, (2 : ℝ) ^ x + 3 = 0 
    have eq8 : (2 : ℝ) ^ x = -3 := by linarith 
    nlinarith [show (0 : ℝ) < (2 : ℝ) ^ x from by positivity]
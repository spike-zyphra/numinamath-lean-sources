import Mathlib

theorem algebra_16161 (m M : ℝ) (hm : IsLeast {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} m) (hM : IsGreatest {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} M) : M + 10 * m = 28 := by
  have h1 : m ≥ -2 := by
    have h9 : ∀ t, t ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} → t ≥ -2 := by 
      intro t ht 
      rcases ht with ⟨x, y, z, ht1, ht2⟩ 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - 2), sq_nonneg (x + y + z - 12)]
    have h7 : m ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} := hm.1 
    specialize h9 m h7 
    linarith
  have h3 : m ≤ -2 := by
    have h4 : -2 ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} := by 
      use (2 + Real.sqrt 10) / 3, (2 + Real.sqrt 10) / 3, (2 - 2 * Real.sqrt 10) / 3
      constructor
      · -- Show that with these variables, the value is -2
        nlinarith [Real.sqrt_pos.mpr (show (10 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
      · -- Show that with these variables, the constraint is met
        nlinarith [Real.sqrt_pos.mpr (show (10 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (10 : ℝ) by norm_num)]
    apply hm.2 h4 
  have h10 : m = -2 := by
    linarith
  have h5 : M ≥ 48 := by
    have h4 : (48 : ℝ) ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} := by 
      use 4, 4, 4 
      constructor
      · norm_num 
      · norm_num
    apply hM.2 h4
  have h2 : M ≤ 48 := by 
    have h9 : ∀ t, t ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} → t ≤ 48 := by 
      intro t ht 
      rcases ht with ⟨x, y, z, ht1, ht2⟩ 
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x + y + z - 12)]
    have h7 : M ∈ {t : ℝ | ∃ x y z, t = x * y + x * z + y * z ∧ 4 * (x + y + z) = x ^ 2 + y ^ 2 + z ^ 2} := hM.1 
    specialize h9 M h7 
    linarith 
  have hM_eq48 : M = 48 := by 
    linarith 
  linarith [hM_eq48, h10]
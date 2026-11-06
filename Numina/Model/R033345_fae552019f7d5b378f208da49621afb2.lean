import Mathlib

theorem algebra_256977 (k : ℝ) :
    ∃ x : ℝ, x ≠ 1 ∧ x ≠ 2 ∧ x = k^2 * (x - 1) * (x - 2) := by
  by_cases hk : k = 0
  · -- When k = 0, x = 0 is a solution.
    use (0 : ℝ)
    constructor
    · -- Show 0 ≠ 1
      norm_num
    constructor
    · -- Show 0 ≠ 2
      norm_num
    · -- Show 0 = 0^2 * (0 - 1) * (0 - 2)
      norm_num [hk]
  · -- Case k ≠ 0
    have hk2 : k ≠ 0 := by 
      intro h'
      apply hk
      linarith
    use (3 * k^2 + 1 + Real.sqrt (k^4 + 6 * k^2 + 1)) / (2 * k^2)
    constructor
    · -- Show x ≠ 1
      by_contra h1
      have eq1 : (3 * k^2 + 1 + Real.sqrt (k^4 + 6 * k^2 + 1)) / (2 * k^2) = 1 := by
        linarith [h1]
      have eq2 : 3 * k^2 + 1 + Real.sqrt (k^4 + 6 * k^2 + 1) = 2 * k^2 := by
        have h1' : 2 * k^2 ≠ 0 := by
          have hk' : k^2 > 0 := by
            have : k ≠ 0 := hk2
            have : k^2 > 0 := by 
              exact sq_pos_of_ne_zero this
            linarith
          nlinarith
        field_simp [h1'] at eq1 ⊢
        all_goals
        nlinarith [eq1]
      have eq3 : Real.sqrt (k^4 + 6 * k^2 + 1) = -k^2 - 1 := by
        nlinarith
      have h5 : Real.sqrt (k^4 + 6 * k^2 + 1) ≥ 0 := by
        apply Real.sqrt_nonneg
      -- From eq3 and h5, we get -k^2 - 1 ≥ 0
      have h5' : -k^2 - 1 ≥ (0 : ℝ) := by
        nlinarith [eq3, h5]
      -- Which means k^2 ≤ -1, which is impossible
      -- because k^2 ≥ 0 for real numbers k.
      have h6 : k^2 ≤ (-1 : ℝ) := by
        nlinarith
      have h7 : k^2 ≥ (0 : ℝ) := by 
        nlinarith [sq_nonneg k]
      nlinarith
    constructor
    · -- Show x ≠ 2
      by_contra h2
      have eq1 : (3 * k^2 + 1 + Real.sqrt (k^4 + 6 * k^2 + 1)) / (2 * k^2) = 2 := by
        linarith [h2]
      have eq2 : 3 * k^2 + 1 + Real.sqrt (k^4 + 6 * k^2 + 1) = 4 * k^2 := by
        have h1' : 2 * k^2 ≠ 0 := by
          have hk' : k^2 > 0 := by
            have : k ≠ 0 := hk2
            have : k^2 > 0 := by 
              exact sq_pos_of_ne_zero this
            linarith
          nlinarith
        field_simp [h1'] at eq1 ⊢
        all_goals
        nlinarith [eq1]
      have eq3 : Real.sqrt (k^4 + 6 * k^2 + 1) = k^2 - 1 := by
        nlinarith
      have h5 : Real.sqrt (k^4 + 6 * k^2 + 1) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h5' : k^2 - 1 ≥ (0 : ℝ) := by 
        nlinarith [eq3, h5]
      have h6 : Real.sqrt (k^4 + 6 * k^2 + 1) ^ 2 = (k^2 - 1) ^ 2 := by
        rw [eq3]
      have h7 : Real.sqrt (k^4 + 6 * k^2 + 1) ^ 2 = k^4 + 6 * k^2 + 1 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (k^2), sq_nonneg k, sq_nonneg (k^4 + 6 * k^2 + 1)]
        all_goals nlinarith
      have eq8 : k^4 + 6 * k^2 + 1 = (k^2 - 1)^2 := by
        nlinarith [h6, h7]
      have eq9 : (k^2 - 1)^2 = k^4 - 2 * k^2 + 1 := by
        nlinarith
      have eq10 : k^2 = 0 := by
        nlinarith [eq8, eq9]
      have eq11 : k = 0 := by
        nlinarith
      tauto
    · -- Show x = k^2 * (x - 1) * (x - 2)
      field_simp
      nlinarith [Real.sqrt_nonneg (k^4 + 6 * k^2 + 1), 
        Real.sq_sqrt (show k^4 + 6 * k^2 + 1 ≥ 0 by nlinarith [sq_nonneg (k^2), sq_nonneg k, sq_nonneg (k^4 + 6 * k^2 + 1)])]
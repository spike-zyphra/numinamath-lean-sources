import Mathlib

theorem algebra_224927 (f : ℝ → ℝ) (hf : f = fun x => x * abs x - 3 * abs x + 2) :
    {x | f x = 0}.ncard = 3 := by
  have h1 : {x | f x = 0} = {1, 2, (3 - Real.sqrt 17) / 2} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(x) = 0, prove x ∈ {1, 2, (3 - Real.sqrt 17) / 2}
      intro h_eq
      by_cases h : x ≥ 0
      · -- If x ≥ 0.
        have h2 : abs x = x := abs_of_nonneg h
        rw [h2] at h_eq
        have h3 : x * x - 3 * x + 2 = 0 := by
          linarith
        have : (x - 1) * (x - 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp this) with h4 h5
        · -- Case x - 1 = 0, so x = 1
          left
          linarith
        · -- Case x - 2 = 0, so x = 2
          right
          left
          linarith
      · -- Case x < 0.
        have h2 : abs x = -x := abs_of_neg (lt_of_not_ge h)
        rw [h2] at h_eq
        have h_eq2 : -x ^ 2 + 3 * x + 2 = 0 := by
          nlinarith
        have h_eq3 : x ^ 2 - 3 * x - 2 = 0 := by
          nlinarith
        have h_eq4 : x < 0 := by linarith
        have h_c : x = (3 - Real.sqrt 17) / 2 := by
          have h_eq3 : x ^ 2 - 3 * x - 2 = 0 := h_eq3
          have h_eq4 : x < 0 := h_eq4
          have h_eq5 : (x - (3 + Real.sqrt 17) / 2) * (x - (3 - Real.sqrt 17) / 2) = 0 := by 
            nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
          cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
          · -- Case where x = (3 + Real.sqrt 17) / 2 (positive root)
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (17 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
          · -- Case where x = (3 - Real.sqrt 17) / 2 (negative root)
            linarith
        right
        right
        linarith
    · -- Assume x ∈ {1, 2, (3 - Real.sqrt 17) / 2}, prove f(x) = 0
      rintro (rfl | rfl | rfl)
      · -- Case x = 1.
        norm_num [abs_of_nonneg]
      · -- Case x = 2.
        norm_num [abs_of_nonneg]
      · -- Case x = (3 - Real.sqrt 17) / 2.
        have h4 : (3 - Real.sqrt 17) / 2 < 0 := by
          have h5 : Real.sqrt 17 > (3 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num), sq_nonneg (Real.sqrt 17 - 3)]
          nlinarith
        have h5 : abs ((3 - Real.sqrt 17) / 2 : ℝ) = -((3 - Real.sqrt 17) / 2) := by
          rw [abs_of_neg h4]
        rw [h5]
        field_simp
        nlinarith [Real.sqrt_nonneg 17, Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  rw [h1]
  have h2 : (1 : ℝ) ≠ (2 : ℝ) := by
    norm_num
  have h3 : (1 : ℝ) ≠ (3 - Real.sqrt 17) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (17 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  have h4 : (2 : ℝ) ≠ (3 - Real.sqrt 17) / 2 := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (17 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (17 : ℝ) by norm_num)]
  rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num [h2, h3, h4]
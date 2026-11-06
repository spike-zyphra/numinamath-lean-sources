import Mathlib

theorem algebra_20720 (f : ℝ → ℝ) (hf : f = fun x => x ^ 4 - 2 * x ^ 2 - 7) :
    Set.ncard {x | f x = 0} = 2 := by

  have h1 : {x | f x = 0} = {Real.sqrt (1 + 2 * Real.sqrt 2), -Real.sqrt (1 + 2 * Real.sqrt 2)} := by
    ext x
    simp [hf]
    constructor
    · -- Assume f x = 0, prove x ∈ {±√(1 + 2√2)}
      intro h_eq
      have h2 : x^4 - 2 * x^2 - 7 = 0 := by
        simpa using h_eq
      have h3 : (x ^ 2) ^ 2 - 2 * (x ^ 2) - 7 = 0 := by
        nlinarith
      have h4 : (x ^ 2 - (1 + 2 * Real.sqrt 2)) * (x ^ 2 - (1 - 2 * Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h4) with h5 h6
      · -- Case where x^2 = 1 + 2√2
        have h7 : x ^ 2 = 1 + 2 * Real.sqrt 2 := by linarith
        have h8 : x = Real.sqrt (1 + 2 * Real.sqrt 2) ∨ x = -Real.sqrt (1 + 2 * Real.sqrt 2) := by
          have h10 : Real.sqrt (x ^ 2) = Real.sqrt (1 + 2 * Real.sqrt 2) := by
            rw [h7]
          have h11 : Real.sqrt (x ^ 2) = |x| := by
            rw [Real.sqrt_sq_eq_abs]
          rw [h11] at h10
          cases eq_or_eq_neg_of_abs_eq h10 with
          | inl h12 =>
            left
            linarith
          | inr h13 =>
            right
            linarith
        tauto
      · -- Case where x^2 = 1 - 2√2 (impossible)
        have h7 : x ^ 2 = 1 - 2 * Real.sqrt 2 := by linarith
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg x, sq_nonneg (Real.sqrt 2 - 1)]
    · -- Assume x ∈ {±√(1 + 2√2)}, prove f x = 0
      rintro (rfl | rfl)
      · -- Case where x = Real.sqrt (1 + 2 * Real.sqrt 2)
        have h_eq1 : (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 - 2 * (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 - 7 = 0 := by
          have hsq : (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 = 1 + 2 * Real.sqrt 2 := by
            rw [Real.sq_sqrt]
            have f2m : (0 : ℝ) ≤ 1 + 2 * Real.sqrt 2 := by
              nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            exact f2m
          have ha3 : (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 = (1 + 2 * Real.sqrt 2) ^ 2 := by
            calc
              (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 = ((Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2) ^ 2 := by ring
              _ = (1 + 2 * Real.sqrt 2) ^ 2 := by rw [hsq]
          nlinarith [ha3, hsq, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        linarith [h_eq1]
      · -- Case where x = -Real.sqrt (1 + 2 * Real.sqrt 2)
        have h_eq1 : (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 - 2 * (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 - 7 = 0 := by
          have hsq : (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 = 1 + 2 * Real.sqrt 2 := by
            have h5 : (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 = (Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2 := by
              ring
            rw [h5]
            rw [Real.sq_sqrt]
            have f2m : (0 : ℝ) ≤ 1 + 2 * Real.sqrt 2 := by
              nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
            exact f2m
          have ha3 : (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 = (1 + 2 * Real.sqrt 2) ^ 2 := by
            calc
              (-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 4 = ((-Real.sqrt (1 + 2 * Real.sqrt 2)) ^ 2) ^ 2 := by ring
              _ = (1 + 2 * Real.sqrt 2) ^ 2 := by rw [hsq]
          nlinarith [ha3, hsq, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        linarith [h_eq1]
  rw [h1]
  have h5 : Real.sqrt (1 + 2 * Real.sqrt 2) ≠ -Real.sqrt (1 + 2 * Real.sqrt 2) := by
    have h1_pos : Real.sqrt (1 + 2 * Real.sqrt 2) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h7_neg : -Real.sqrt (1 + 2 * Real.sqrt 2) < 0 := by
      nlinarith [h1_pos]
    linarith [h1_pos, Real.sqrt_nonneg (1 + 2 * Real.sqrt 2)]
  rw [Set.ncard_pair h5]
  all_goals norm_num
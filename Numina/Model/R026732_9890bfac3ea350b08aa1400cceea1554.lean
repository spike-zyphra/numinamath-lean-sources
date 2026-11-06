import Mathlib

theorem algebra_321239 (f g : ℝ → ℝ)
    (hf : f = fun x => x^3 - 3 * x^2 + x - 2)
    (hg : g = fun x => x^3 - x^2 - 4 * x + 7) :
    ∀ x, f x * g x + 6 * x^2 - 15 * x + 18 = 0 ↔
    x = 1 ∨ x = 2 ∨ x = -2 ∨ x = 1 + Real.sqrt 2 ∨ x = 1 - Real.sqrt 2 := by
  intro x
  constructor
  · -- Assume f x * g x + 6 * x^2 - 15 * x + 18 = 0, prove the disjunction of the roots
    intro h
    have h_eq : (x - 1)^2 * (x - 2) * (x + 2) * (x ^ 2 - 2 * x - 1) = 0 := by
      have eq1 : (x^3 - 3 * x^2 + x - 2) * (x^3 - x^2 - 4 * x + 7) + 6 * x ^ 2 - 15 * x + 18 = 0 := by
        simp [hf, hg] at h ⊢
        linarith
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x + 2)]
    cases' (mul_eq_zero.mp h_eq) with h1 h_eq
    · cases' (mul_eq_zero.mp h1) with h1 h_eq
      · cases' (mul_eq_zero.mp h1) with h1 h_eq
        · -- Case where (x - 1)^2 = 0
          have h3 : x - 1 = 0 := by
            apply pow_eq_zero
            exact h1
          left
          linarith
        · -- Case where (x - 2) = 0
          right
          left
          linarith
      · -- Case where (x + 2) = 0
        right
        right
        left
        linarith
    · -- Case where x^2 - 2x - 1 = 0
      have h3 : x ^ 2 - 2 * x - 1 = 0 := by
        linarith
      have h5 : (x - (1 + Real.sqrt 2)) * (x - (1 - Real.sqrt 2)) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      cases' (mul_eq_zero.mp h5) with h6 h7
      · -- Case where x - (1 + Real.sqrt 2) = 0
        right
        right
        right
        left
        linarith
      · -- Case where x - (1 - Real.sqrt 2) = 0
        right
        right
        right
        right
        linarith
  · -- Assume the disjunction of the roots, prove f x * g x + 6 * x^2 - 15 * x + 18 = 0
    rintro (h | h | h | h | h)
    · -- Case where x = 1
      rw [h]
      norm_num [hf, hg]
    · -- Case where x = 2
      rw [h]
      norm_num [hf, hg]
    · -- Case where x = -2
      rw [h]
      norm_num [hf, hg]
    · -- Case where x = 1 + Real.sqrt 2
      rw [h]
      have eq1 : ((1 + Real.sqrt 2 : ℝ) : ℝ) ^ 2 - 2 * ((1 + Real.sqrt 2 : ℝ) : ℝ) - 1 = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have eq2 : ((1 + Real.sqrt 2 : ℝ) ^ 3 - 3 * (1 + Real.sqrt 2 : ℝ) ^ 2 + (1 + Real.sqrt 2 : ℝ) - 2) * ((1 + Real.sqrt 2 : ℝ) ^ 3 - (1 + Real.sqrt 2 : ℝ) ^ 2 - 4 * (1 + Real.sqrt 2 : ℝ) + 7) + 6 * (1 + Real.sqrt 2 : ℝ) ^ 2 - 15 * (1 + Real.sqrt 2 : ℝ) + 18 = 0 := by
        have eq3 : ((1 + Real.sqrt 2 : ℝ) ^ 2 - 2 * (1 + Real.sqrt 2 : ℝ) - 1) = 0 := by
          linarith [eq1]
        have eq4 : ((1 + Real.sqrt 2 : ℝ) ^ 3 - 3 * (1 + Real.sqrt 2 : ℝ) ^ 2 + (1 + Real.sqrt 2 : ℝ) - 2) * ((1 + Real.sqrt 2 : ℝ) ^ 3 - (1 + Real.sqrt 2 : ℝ) ^ 2 - 4 * (1 + Real.sqrt 2 : ℝ) + 7) + 6 * (1 + Real.sqrt 2 : ℝ) ^ 2 - 15 * (1 + Real.sqrt 2 : ℝ) + 18 = ((1 + Real.sqrt 2 : ℝ) - 1) ^ 2 * ((1 + Real.sqrt 2 : ℝ) - 2) * ((1 + Real.sqrt 2 : ℝ) + 2) * (((1 + Real.sqrt 2 : ℝ) ^ 2 - 2 * (1 + Real.sqrt 2 : ℝ) - 1)) := by 
          nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg ((1 + Real.sqrt 2) ^ 2 - 2 * (1 + Real.sqrt 2) - 1)]
        rw [eq4]
        rw [eq3]
        all_goals norm_num
      simpa [hf, hg] using eq2
    · -- Case where x = 1 - Real.sqrt 2
      rw [h]
      have eq1 : ((1 - Real.sqrt 2 : ℝ) : ℝ) ^ 2 - 2 * ((1 - Real.sqrt 2 : ℝ) : ℝ) - 1 = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have eq2 : ((1 - Real.sqrt 2 : ℝ) ^ 3 - 3 * (1 - Real.sqrt 2 : ℝ) ^ 2 + (1 - Real.sqrt 2 : ℝ) - 2) * ((1 - Real.sqrt 2 : ℝ) ^ 3 - (1 - Real.sqrt 2 : ℝ) ^ 2 - 4 * (1 - Real.sqrt 2 : ℝ) + 7) + 6 * (1 - Real.sqrt 2 : ℝ) ^ 2 - 15 * (1 - Real.sqrt 2 : ℝ) + 18 = 0 := by
        have eq3 : ((1 - Real.sqrt 2 : ℝ) ^ 2 - 2 * (1 - Real.sqrt 2 : ℝ) - 1) = 0 := by
          linarith [eq1]
        have eq4 : ((1 - Real.sqrt 2 : ℝ) ^ 3 - 3 * (1 - Real.sqrt 2 : ℝ) ^ 2 + (1 - Real.sqrt 2 : ℝ) - 2) * ((1 - Real.sqrt 2 : ℝ) ^ 3 - (1 - Real.sqrt 2 : ℝ) ^ 2 - 4 * (1 - Real.sqrt 2 : ℝ) + 7) + 6 * (1 - Real.sqrt 2 : ℝ) ^ 2 - 15 * (1 - Real.sqrt 2 : ℝ) + 18 = ((1 - Real.sqrt 2 : ℝ) - 1) ^ 2 * ((1 - Real.sqrt 2 : ℝ) - 2) * ((1 - Real.sqrt 2 : ℝ) + 2) * (((1 - Real.sqrt 2 : ℝ) ^ 2 - 2 * (1 - Real.sqrt 2 : ℝ) - 1)) := by
          nlinarith [sq_pos_of_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2), sq_nonneg ((1 - Real.sqrt 2) ^ 2 - 2 * (1 - Real.sqrt 2) - 1)]
        rw [eq4]
        rw [eq3]
        all_goals norm_num
      simpa [hf, hg] using eq2
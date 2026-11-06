import Mathlib

theorem algebra_222803 (f : ℝ → ℝ) (hf : f = fun x => x^2 + 25 * x + 52) :
    ∏ᶠ x ∈ {x | f x = 3 * Real.sqrt (x^2 + 25 * x + 80)}, x = 31 := by
  have h1 : {x | f x = 3 * Real.sqrt (x^2 + 25 * x + 80)} = {(-25 + Real.sqrt 501) / 2, (-25 - Real.sqrt 501) / 2} := by
    ext x
    simp [hf]
    constructor
    · -- Assume x^2 + 25 x + 52 = 3 √(x^2 + 25 x + 80)
      intro h_eq
      have h4 : Real.sqrt (x ^ 2 + 25 * x + 80) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 25 * x + 80)
      have h5 : x^2 + 25 * x + 80 ≥ 0 := by 
        by_contra h
        push_neg at h
        have h2 : Real.sqrt (x^2 + 25 * x + 80) = 0 := by
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith
        rw [h2] at h_eq
        nlinarith
      have h6 : x^2 + 25 * x + 52 = 3 * Real.sqrt (x^2 + 25 * x + 80) := by linarith
      have eq1 : (Real.sqrt (x^2 + 25 * x + 80))^2 = x^2 + 25 * x + 80 := by
        apply Real.sq_sqrt 
        linarith
      have eq4 : (Real.sqrt (x^2 + 25 * x + 80) - 7) * (Real.sqrt (x^2 + 25 * x + 80) + 4) = 0 := by 
        nlinarith [sq_nonneg (Real.sqrt (x^2 + 25 * x + 80) - 7), sq_nonneg (Real.sqrt (x^2 + 25 * x + 80) ^ 2), Real.sqrt_nonneg (x^2 + 25 * x + 80), h6, Real.sq_sqrt (show 0 ≤ (x^2 + 25 * x + 80 : ℝ) by linarith)]
      cases' (mul_eq_zero.mp eq4) with h6 h6
      · -- Case √(x^2 + 25 * x + 80) - 7 = 0.
        have eq10 : Real.sqrt (x^2 + 25 * x + 80) = 7 := by linarith
        have eq11 : x^2 + 25 * x + 80 = 49 := by 
          calc
            x^2 + 25 * x + 80 = (Real.sqrt (x^2 + 25 * x + 80)) ^ 2 := by 
              rw [Real.sq_sqrt]
              linarith
            _ = (7 : ℝ) ^ 2 := by 
              rw [eq10]
            _ = (49 : ℝ) := by norm_num
        have h8 : x^2 + 25 * x + 31 = 0 := by 
          nlinarith
        have h_eq7 : x^2 + 25 * x + 31 = (x - (-25 + Real.sqrt 501) / 2) * (x - (-25 - Real.sqrt 501) / 2) := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 (h_eq7.symm ▸ h8)) with h_eq8 h_eq9
        · -- x - (-25 + Real.sqrt 501) / 2 = 0 
          left
          linarith
        · -- x - (-25 - Real.sqrt 501) / 2 = 0 
          right
          linarith
      · -- Case √(x^2 + 25 * x + 80) + 4 = 0. 
        nlinarith [show Real.sqrt (x^2 + 25 * x + 80) ≥ 0 by apply Real.sqrt_nonneg]
    · -- Show that both roots in the right-hand side set satisfy the original equation
      rintro (h_eq | h_eq)
      · -- Case $x = (-25 + \sqrt(501))/2$
        rw [h_eq]
        have h_eq6 : ((-25 + Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 + Real.sqrt 501) / 2) + 52 = 21 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
        have h_eq7 : ((-25 + Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 + Real.sqrt 501) / 2) + 80 = (49 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
        have h_eq8 : Real.sqrt (((-25 + Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 + Real.sqrt 501) / 2) + 80) = 7 := by
          rw [h_eq7]
          have : Real.sqrt (49 : ℝ) = 7 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          linarith
        nlinarith [h_eq6, h_eq8]
      · -- Case $x = (-25 - \sqrt(501))/2$
        rw [h_eq]
        have h_eq6 : ((-25 - Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 - Real.sqrt 501) / 2) + 52 = 21 := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
        have h_eq7 : ((-25 - Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 - Real.sqrt 501) / 2) + 80 = (49 : ℝ) := by
          nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
        have h_eq8 : Real.sqrt (((-25 - Real.sqrt 501) / 2) ^ 2 + 25 * ((-25 - Real.sqrt 501) / 2) + 80) = 7 := by
          rw [h_eq7]
          have : Real.sqrt (49 : ℝ) = 7 := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          linarith
        nlinarith [h_eq6, h_eq8]
  rw [h1]
  rw [finprod_mem_pair (by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
  )]
  <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (501 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (501 : ℝ) by norm_num)]
import Mathlib

theorem algebra_171268 (f : ℝ → ℝ) (m : ℝ) (hf : f = fun x => 9^x - m * 3^x + m + 1)
    (h : ∀ x > 0, f x > 0) : m < 2 + 2 * √2 := by
  by_contra h1
  have h2 : m ≥ 2 + 2 * √2 := by linarith
  have h3 : ∃ x > (0 : ℝ), f x ≤ 0 := by
    use (Real.logb (3 : ℝ) (1 + Real.sqrt 2))
    constructor
    · -- Show that x > 0
      have h4 : (1 + Real.sqrt 2 : ℝ) > (1 : ℝ) := by
        have h5 : Real.sqrt 2 > 0 := by positivity
        linarith
      have h5 : Real.logb (3 : ℝ) (1 + Real.sqrt 2) > (0 : ℝ) := by
        apply Real.logb_pos
        all_goals linarith
      linarith
    · -- Show f(x) ≤ 0
      rw [hf]
      simp
      have h6 : (3 : ℝ) ^ ((Real.logb (3 : ℝ) (1 + Real.sqrt 2)) : ℝ) = (1 + Real.sqrt 2 : ℝ) := by
        rw [Real.rpow_logb]
        all_goals
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      have h7 : (9 : ℝ) ^ ((Real.logb (3 : ℝ) (1 + Real.sqrt 2)) : ℝ) = (1 + Real.sqrt 2 : ℝ) ^ 2 := by
        have h8 : (9 : ℝ) ^ ((Real.logb (3 : ℝ) (1 + Real.sqrt 2)) : ℝ) = ((3 : ℝ) ^ (2 : ℝ) ) ^ ((Real.logb (3 : ℝ) (1 + Real.sqrt 2)) : ℝ) := by norm_num
        rw [h8]
        rw [← Real.rpow_mul]
        have h9 : (3 : ℝ) ^ (2 * (Real.logb (3 : ℝ) (1 + Real.sqrt 2) : ℝ) ) = ((3 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) : ℝ) ) ^ 2 := by
          calc
            (3 : ℝ) ^ (2 * (Real.logb (3 : ℝ) (1 + Real.sqrt 2) : ℝ) ) = (3 : ℝ) ^ (2 * (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) := by ring
            _ = ((3 : ℝ) ^ (Real.logb (3 : ℝ) (1 + Real.sqrt 2) ) ) ^ 2 := by
              rw [← Real.rpow_natCast]
              rw [← Real.rpow_mul]
              ring
              all_goals positivity
        rw [h9]
        rw [h6]
        all_goals norm_num
      rw [h7, h6]
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (m - (2 + 2 * Real.sqrt 2)), Real.sqrt_nonneg 2]
  rcases h3 with ⟨x, hx1, hx2⟩
  have hx3 : f x > 0 := h x hx1
  linarith
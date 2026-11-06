import Mathlib

theorem algebra_302520 (a : ℝ) (h : ∃! x : ℝ, x^2 + a * abs x + a^2 - 3 = 0) :
    a = Real.sqrt 3 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have h1 : x^2 + a * abs x + a^2 - 3 = 0 := hx1
  have h2 : ∀ y, y ^ 2 + a * abs y + a ^ 2 - 3 = 0 → y = x := by
    intro y hy
    exact hx2 y hy
  -- Check if -x is also a solution
  have h4 : (-x) ^ 2 + a * abs (-x) + a ^ 2 - 3 = 0 := by
    have h5 : abs (-x) = abs x := by
      simp [abs_neg]
    rw [h5]
    nlinarith [h1]
  -- From uniqueness of solution, -x = x
  have h4_eq : -x = x := by
    apply h2 (-x)
    all_goals linarith [h4]
  have hx3 : x = 0 := by linarith [h4_eq]
  rw [hx3] at h1
  have h1_eq : a ^ 2 = 3 := by
    norm_num [abs_of_nonneg (show (0 : ℝ) ≥ 0 by linarith)] at h1
    nlinarith
  by_cases h50 : a > 0
  · -- If a > 0: a^2 = 3 => a = sqrt 3
    have ha2 : a = Real.sqrt 3 := by
      have h5 : a ^ 2 = 3 := h1_eq
      have ha2 : a > 0 := h50
      have h6 : a = Real.sqrt 3 := by
        rw [← h5]
        field_simp
      exact h6
    exact ha2
  · -- a ≤ 0
    by_cases h51 : a = 0
    · -- a = 0
      rw [h51] at h1_eq
      nlinarith
    · -- a < 0
      have n51 : a < (0 : ℝ) := by
        by_contra h7
        push_neg at h7
        have h8 : a = 0 := by
          linarith
        tauto
      have h9 := h2 (Real.sqrt 3)
      have h9_eq : (Real.sqrt 3) ^ 2 + a * abs (Real.sqrt 3) + a ^ 2 - 3 = 0 := by
        have h5 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith)
        have h6 : abs (Real.sqrt 3) = Real.sqrt 3 := by
          apply abs_of_nonneg
          apply Real.sqrt_nonneg
        rw [h6]
        nlinarith [h5, Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by linarith), h1_eq]
      have eq1 := h9 (by
        linarith [h9_eq]
      )
      have s2 := Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num)
      nlinarith
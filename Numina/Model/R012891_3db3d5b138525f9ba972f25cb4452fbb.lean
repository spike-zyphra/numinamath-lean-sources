import Mathlib

theorem algebra_188366 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : Real.logb 10 (x^2 + y^2) = 2) (h2 : Real.logb 2 x - 4 = Real.logb 2 3 - Real.logb 2 y) :
    (x = 8 ∧ y = 6) ∨ (x = 6 ∧ y = 8) := by

  have eq1 : x^2 + y^2 = 100 := by
    have h3 : x^2 + y^2 > 0 := by
      nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
    have h4 : Real.logb 10 (x^2 + y^2) = 2 := h1
    rw [Real.logb_eq_iff_rpow_eq] at h4
    · -- Show that x^2 + y^2 = 100
      nlinarith
    all_goals
      nlinarith

  -- Convert h2 to $x * y = 48$
  have eq2 : x * y = 48 := by
    have h5 : Real.logb 2 x - 4 = Real.logb 2 3 - Real.logb 2 y := h2

    -- Rewrite h5
    have h6 : Real.logb 2 x - Real.logb 2 3 = 4 - Real.logb 2 y := by
      linarith

    -- Convert h6 to logarithm form
    have h7 : Real.logb 2 (x / 3) = Real.logb 2 x - Real.logb 2 3 := by
      rw [Real.logb_div (by linarith) (by norm_num)]

    -- Substitute h7 into h6
    have h8 : Real.logb 2 (x / 3) = 4 - Real.logb 2 y := by
      linarith [h6, h7]

    -- Convert $4$ to $\log_2 16$
    have h9 : Real.logb 2 (16 / y) = Real.logb 2 16 - Real.logb 2 y := by
      rw [Real.logb_div (by positivity) (by positivity)]

    -- $\log_2 16 = 4$
    have h10 : Real.logb 2 (16 : ℝ) = (4 : ℝ) := by
      rw [Real.logb_eq_iff_rpow_eq] <;> (norm_num)

    -- Substitute h10 into h9
    have h11 : Real.logb 2 (16 / y) = (4 : ℝ) - Real.logb 2 y := by
      rw [h9, h10]

    -- Equate $\log_2(x/3) = \log_2(16/ y)$
    have h12 : Real.logb 2 (x / 3) = Real.logb 2 (16 / y) := by
      linarith [h8, h11]

    -- Use injective property of logarithm
    have h13 : x / 3 = 16 / y := by
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) h12

    -- Convert h13 to $x * y = 48$
    field_simp at h13 ⊢
    nlinarith [h13]

  -- Now solve eq1 and eq2

  have eq3 : (x + y) ^ 2 = 196 := by
    nlinarith [eq1, eq2]

  have eq4 : x + y = 14 := by
    have h14 : (x + y) ^ 2 = 196 := eq3
    nlinarith [show (x + y : ℝ) > 0 by positivity]

  -- Now prove the quadratic solutions
  have h15 : (x - 8) * (x - 6) = 0 := by
    have h16 : y = 14 - x := by
      linarith
    rw [h16] at eq2
    nlinarith

  cases' (mul_eq_zero.mp h15) with h18 h19

  · -- Case x = 8, then y = 6
    have h20 : x = 8 := by linarith
    have h21 : y = 6 := by
      nlinarith
    left
    exact ⟨h20, h21⟩

  · -- Case x = 6, then y = 8
    have h22 : x = 6 := by linarith
    have h23 : y = 8 := by
      nlinarith
    right
    exact ⟨h22, h23⟩
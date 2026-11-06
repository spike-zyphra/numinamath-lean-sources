import Mathlib

theorem algebra_173675 (a : ℝ) (h : ∃! x : ℝ, x^2 + a * abs x + a^2 - 3 = 0) :
    a = Real.sqrt 3 := by
  rcases h with ⟨x, ⟨hx1, hx2⟩⟩
  have hx0 : x = 0 := by
    have h_eq : (-x) ^ 2 + a * abs (-x) + a ^ 2 - 3 = 0 := by
      have h2 : (-x) ^ 2 + a * abs (-x) + a ^ 2 - 3 = x^2 + a * abs x + a ^ 2 - 3 := by
        have habs : abs (-x) = abs x := by
          simp [abs_neg]
        rw [habs]
        <;> ring
      rw [h2]
      exact hx1
    have h_eq' : ∀ y : ℝ, (y : ℝ) ^ 2 + a * abs y + a ^ 2 - 3 = 0 → y = x := by
      intro y hy
      linarith [hx2 y hy]
    have h_eq1 : -x = x := by
      apply h_eq' (-x)
      exact h_eq
    have hx0 : x = 0 := by
      linarith
    exact hx0
  have hx00 : x ^ 2 + a * abs x + a^2 - 3 = 0 := hx1
  rw [show x = (0 : ℝ) by linarith] at hx00
  have h3 : a^2 = 3 := by
    simp [abs_zero] at hx00
    nlinarith
  have h4 : a = Real.sqrt 3 := by
    have h5 : a ^ 2 = 3 := h3
    have h6 : a = Real.sqrt 3 ∨ a = -Real.sqrt 3 := by
      have h6 : a ^ 2 = 3 := h5
      have h7 : (a - Real.sqrt 3) * (a + Real.sqrt 3) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      cases (mul_eq_zero.mp h7) with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        linarith
    rcases h6 with h | h
    .
      exact h
    .
      have ha1 : a = -Real.sqrt 3 := h
      have h6 : (Real.sqrt 3) ^ 2 + a * abs (Real.sqrt 3) + a^2 - 3 = 0 := by
        rw [ha1]
        have hx9 : abs (Real.sqrt 3) = Real.sqrt 3 := by
          simp [abs_of_pos, show Real.sqrt 3 > 0 by positivity]
        rw [hx9]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
      -- Show x = sqrt 3 also satisfies it, but unique solution is x=0.
      have htrace := hx2 (Real.sqrt 3) (by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sqrt_nonneg 3, h6]
          )
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sqrt_nonneg 3]
  exact h4
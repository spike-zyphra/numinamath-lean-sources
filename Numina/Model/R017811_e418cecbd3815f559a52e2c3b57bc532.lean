import Mathlib

theorem algebra_294069 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h1 : ∃ a b, 0 ≤ a ∧ a ≤ x ∧ 0 ≤ b ∧ b ≤ y ∧ a^2 + y^2 = 2 ∧ b^2 + x^2 = 1 ∧ a * x + b * y = 1) :
    x + y ≤ Real.sqrt 5 := by
  rcases h1 with ⟨a, b, ha, hax, hb, hby, ha2, hb2, h3⟩
  have h4 : (x + y) ^ 2 ≤ 5 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (x - y), sq_nonneg (a * y + b * x), sq_nonneg (a * x - b * y), sq_nonneg (x * y - a * b), mul_pos hx hy, mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hby)]
  have h5 : x + y ≤ Real.sqrt 5 := by
    have h6 : (x + y) ^ 2 ≤ 5 := h4
    have h7 : x + y ≥ 0 := by linarith
    have h8 : Real.sqrt ((x + y) ^ 2) ≤ Real.sqrt (5 : ℝ) := by
      apply Real.sqrt_le_sqrt
      linarith
    have h9 : Real.sqrt ((x + y) ^ 2) = x + y := by
      rw [Real.sqrt_sq (show 0 ≤ (x + y : ℝ) by linarith)]
    linarith [h9, h8]
  exact h5
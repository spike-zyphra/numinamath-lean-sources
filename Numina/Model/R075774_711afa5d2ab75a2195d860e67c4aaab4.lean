import Mathlib

theorem algebra_1565
  (a b c d : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h₁ : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d)
  (h₂ : a > b ∧ a > c ∧ a > d)
  (h₃ : d < b ∧ d < c)
  (h₄ : a / b = c / d)
  : (a + d > b + c) := by
  rcases h₀ with ⟨ha, hb, hc, hd⟩
  rcases h₁ with ⟨ha1, ha2, ha3, hb1, hb2, hc1⟩
  rcases h₂ with ⟨h7, h8, h9⟩
  rcases h₃ with ⟨h10, h11⟩
  have h5 : a * d = b * c := by
    have hb' : b ≠ 0 := by linarith
    have hd' : d ≠ 0 := by linarith
    field_simp [hb', hd'] at h₄
    linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (d - b), sq_nonneg (d - c), sq_nonneg (b - c), sq_pos_of_ne_zero (sub_ne_zero_of_ne ha1), sq_pos_of_ne_zero (sub_ne_zero_of_ne ha2), sq_pos_of_ne_zero (sub_ne_zero_of_ne ha3), sq_pos_of_ne_zero (sub_ne_zero_of_ne hb1), sq_pos_of_ne_zero (sub_ne_zero_of_ne hb2), sq_pos_of_ne_zero (sub_ne_zero_of_ne hc1)]
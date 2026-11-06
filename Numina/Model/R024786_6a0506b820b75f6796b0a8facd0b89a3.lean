import Mathlib

theorem algebra_317907 (a b : ℝ) (h : ∃ x1 x2 : ℝ, x1 ∈ Set.Icc 1 2 ∧ x2 ∈ Set.Icc 1 2 ∧
    x1^2 + a * x1 + b - 3 = 0 ∧ x2^2 + a * x2 + b - 3 = 0) :
    a^2 + (b - 4)^2 ≥ 2 := by
  rcases h with ⟨x1, x2, hx1, hx2, h1, h2⟩
  rcases hx1 with ⟨hx11, hx12⟩
  rcases hx2 with ⟨hx21, hx22⟩
  nlinarith [sq_nonneg (a + 1), sq_nonneg (b - 3), sq_nonneg (x1 - 1), sq_nonneg (x2 - 1), 
          sq_nonneg (x1 + a + x2), sq_nonneg (b - 3 - x1 * x2), 
          mul_nonneg (sub_nonneg.mpr hx11) (sub_nonneg.mpr hx12), 
          mul_nonneg (sub_nonneg.mpr hx21) (sub_nonneg.mpr hx22)]
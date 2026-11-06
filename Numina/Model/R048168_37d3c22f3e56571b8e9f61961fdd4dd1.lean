import Mathlib

open Real

theorem algebra_150496 (f : ℝ → ℝ)
    (h₀ : ∀ x, 0 < x → f x = ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3))) :
    IsLeast {y | ∃ x, 0 < x ∧ f x = y} (7/3) := by
  constructor
  · -- Show 7/3 is achievable by using x=1
    use 1
    constructor
    · norm_num
    · -- Compute f 1
      rw [h₀ 1 (by norm_num)]
      norm_num
  · -- Show that 7/3 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx⟩
    have h1 : f x = ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3)) := by
      apply h₀ x hx_pos
    rw [h1] at hfx
    have h2 : ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3)) ≥ 7/3 := by
      have hx1 : 0 < x := by linarith
      have hx2 : 0 < x^4 := by positivity
      have hx3 : 0 < x^3 := by positivity
      have hx4 : 0 < x^2 := by positivity
      have h3 : (x + 1/x) ^ 4 - (x ^ 4 + 1 / x ^ 4) = 4 * x^2 + 6 + 4 / x^2 := by
        field_simp
        ring
      have h4 : (x + 1/x) ^ 3 - (x^3 + 1 / x^3) = 3 * x + 3 / x := by
        field_simp
        ring
      have h5 : ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3)) = (4 * x^4 + 6 * x^2 + 4) / (3 * x^3 + 3 * x) := by
        rw [h3, h4]
        have h6 : (4 * x^2 + 6 + 4 / x^2) / (3 * x + 3 / x) = (4 * x^4 + 6 * x^2 + 4) / (3 * x^3 + 3 * x) := by
          field_simp
          ring
        linarith [h6]
      rw [h5]
      have h9 : 0 < 3 * x^3 + 3 * x := by
        nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2), sq_pos_of_pos hx1]
      apply (le_div_iff₀ h9).mpr
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x * (x - 1)), mul_pos hx1 hx2, mul_pos hx1 hx3, sq_nonneg (x ^ 2 + x), sq_nonneg (x ^ 2 + 1)]
    linarith [h2, hfx]
import Mathlib

open Real

theorem algebra_203073 (f : ℝ → ℝ)
    (h₀ : ∀ x, 0 < x → f x = ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3))) :
    IsLeast {y | ∃ x, 0 < x ∧ f x = y} 6 := by
  constructor
  · -- Show 6 is achievable, by x = 1
    use 1
    constructor
    · norm_num
    · -- Show f 1 = 6
      rw [h₀ 1 (by norm_num)]
      norm_num
  · -- Show 6 is minimal
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx⟩
    rw [h₀ x hx_pos] at hfx
    have eq1 : ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) = 3 * (x + 1 / x) := by
      field_simp
      ring_nf
    have eq3 : x + 1 / x ≥ 2 := by
      have h1 : x + 1 / x - 2 ≥ 0 := by
        have h2 : x + 1 / x - 2 = (x - 1) ^ 2 / x := by
          field_simp
          ring
        rw [h2]
        apply div_nonneg
        · -- Show (x - 1)^2 ≥ 0
          apply pow_two_nonneg
        · -- Show x > 0
          linarith [hx_pos]
      linarith
    have eq4 : 3 * (x + 1 / x) ≥ 6 := by
      linarith [eq3]
    have h1 : ((x + 1 / x) ^ 6 - (x ^ 6 + 1 / x ^ 6) - 2) / ((x + 1 / x) ^ 3 + (x ^ 3 + 1 / x ^ 3)) = 3 * (x + 1 / x) := eq1
    linarith [hfx, h1, eq4]
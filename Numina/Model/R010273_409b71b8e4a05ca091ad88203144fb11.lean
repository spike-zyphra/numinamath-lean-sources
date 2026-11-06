import Mathlib
open Real

theorem algebra_9411 (f : ℝ → ℝ) (hf : f = λ x => 4 * x + 25 / x) :
    IsLeast {y | ∃ x > 0, f x = y} 20 := by
  constructor
  · -- Prove that 20 is in the set
    use 5 / 2
    constructor
    · norm_num
    · -- Show that when x = 5/2, then f(x) = 20.
      rw [hf]
      norm_num
  · -- Prove that 20 is the least in the set
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    have h_eq : 4 * x + 25 / x = y := by
      simpa using hfx
    have h1 : 4 * x + 25 / x ≥ 20 := by
      have h2 : x > 0 := hx
      have h3 : 4 * x + 25 / x - 20 ≥ 0 := by
        have h4 : x > 0 := hx
        have h5 : 4 * x + 25 / x - 20 = (4 * x^2 + 25 - 20 * x) / x := by
          field_simp
          ring
        rw [h5]
        have h6 : 4 * x^2 + 25 - 20 * x ≥ 0 := by
          nlinarith [sq_nonneg (2 * x - 5)]
        apply div_nonneg
        linarith
        all_goals linarith
      linarith
    linarith [h_eq, h1]
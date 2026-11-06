import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_215377 (f : ℝ → ℝ) (hf : f = λ x => x^2 - x + 1/x) :
    IsLeast {y | ∃ x > 0, f x = y} 1 := by
  constructor
  · -- Show that 1 is attainable, meaning there exists some x > 0 such that f x = 1
    use 1
    constructor
    · -- Verify 1 > 0
      norm_num
    · -- Evaluate f at 1 and show it equals 1
      rw [hf]
      norm_num
  · -- Now, show that 1 is indeed the smallest value
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx_eq_y⟩
    rw [hf] at hfx_eq_y
    have h_eq : x^2 - x + 1 / x = y := by
      simpa using hfx_eq_y
    -- Show that y >= 1
    have h1 : x^2 - x + 1 / x ≥ 1 := by
      have h_mul : x > 0 := hx_pos
      have h2 : x^2 - x + 1 / x - 1 ≥ 0 := by
        have h3 : x^2 - x + 1 / x - 1 = (x^3 - x^2 - x + 1) / x := by 
          field_simp
          <;> ring
        rw [h3]
        have h4 : x^3 - x^2 - x + 1 ≥ 0 := by
          have h : x^3 - x^2 - x + 1 = (x - 1)^2 * (x + 1) := by
            ring
          rw [h]
          nlinarith [sq_nonneg (x - 1), show (x + 1 > 0) from by linarith
          ]
        have h5 : x > 0 := hx_pos
        apply div_nonneg h4
        linarith
      linarith
    linarith [h_eq, h1]
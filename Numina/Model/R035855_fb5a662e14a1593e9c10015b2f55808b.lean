import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11912 {f : ℝ → ℝ}
  (hf : ∀ x > 0, f x = ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3))) :
  IsLeast {y | ∃ x > 0, f x = y} (7/3) := by
  constructor
  · -- Show 7/3 is in the set
    use 1
    norm_num [hf]
  · -- Show 7/3 is minimal
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have h1 : f x = ((x + 1/x)^4 - (x^4 + 1/x^4)) / ((x + 1/x)^3 - (x^3 + 1/x^3)) := by
      specialize hf x hx
      simpa using hf
    rw [h1] at hfx
    have hx1 : x > 0 := hx
    have hx2 : x + 1 / x ≥ 2 := by
      have hx3 : x > 0 := hx1
      have h4 : x * (1 / x) = 1 := by
        field_simp
      nlinarith [sq_nonneg (x - 1)]
    have eq1 : ((x + 1 / x) ^ 4 - (x ^ 4 + 1 / x ^ 4)) = 4 * (x + 1 / x) ^ 2 - 2 := by
      field_simp
      ring
    have eq2 : ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3)) = 3 * (x + 1 / x) := by 
      field_simp
      ring
    have h2 : ((x + 1 / x) ^ 4 - (x ^ 4 + 1 / x ^ 4)) / ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3)) = (4 / 3) * (x + 1 / x) - (2 / (3 * (x + 1 / x))) := by
      rw [eq1, eq2]
      field_simp
      <;> ring
    rw [h2] at hfx
    have h3 : (4 / 3) * (x + 1 / x) - (2 / (3 * (x + 1 / x))) ≥ 7 / 3 := by
      have h4 : x + 1 / x ≥ 2 := hx2
      have hx7 : x + 1 / x > 0 := by
        have hx8 : x > 0 := hx1
        have hx9 : 1 / x > 0 := by
          apply div_pos
          norm_num
          all_goals linarith
        linarith [show x > 0 by linarith, show 1 / x > 0 by linarith]
      have h7 : (4 / 3) * (x + 1 / x) - (2 / (3 * (x + 1 / x))) - (7 / 3) ≥ 0 := by
        have h8 : x + 1 / x ≥ 2 := h4
        have hx7' : x + 1 / x > 0 := hx7
        have h9 : ( (4 / 3) * (x + 1 / x) - (2 / (3 * (x + 1 / x))) - (7 / 3) ) = (4 * (x + 1 / x) ^ 2 - 2 - 7 * (x + 1 / x)) / (3 * (x + 1 / x)) := by 
          field_simp
          ring
        rw [h9]
        apply div_nonneg
        · -- Numerator non-negative
          nlinarith [sq_nonneg (x + 1 / x - 2), sq_nonneg (x - 1)]
        · -- Denominator positive
          positivity
      linarith
    linarith [hfx, h3]
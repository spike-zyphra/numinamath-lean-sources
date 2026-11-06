import Mathlib

open Real Set

theorem algebra_318041 (f : ℝ → ℝ) (hf : f = fun x => x^2 - x + 1 / x) :
    IsLeast {y | ∃ x, 0 < x ∧ f x = y} 1 := by 
  constructor
  · -- Show that 1 is achievable by f for some x > 0
    use 1
    constructor
    · norm_num
    · -- Calculate f(1) and show it's 1
      rw [hf]
      norm_num
  · -- Show that 1 is the least such value (show that all y in the image are ≥ 1)
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    have h1 : x ^ 2 - x + 1 / x = y := hfx
    have h2 : x ^ 2 - x + 1 / x ≥ 1 := by
      have h3 : x > 0 := hx
      have h4 : x ^ 2 - x + 1 / x - 1 ≥ 0 := by
        have h5 : x ^ 2 - x + 1 / x - 1 = (x ^ 3 - x ^ 2 - x + 1) / x := by
          field_simp
          <;> ring
        rw [h5]
        have h6 : x ^ 3 - x ^ 2 - x + 1 ≥ 0 := by
          have h7 : x ^ 3 - x ^ 2 - x + 1 = (x - 1) ^ 2 * (x + 1) := by
            ring
          rw [h7]
          have h8 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
          have h9 : (x + 1) > 0 := by linarith
          nlinarith [h8, h9]
        have h10 : (x ^ 3 - x ^ 2 - x + 1) / x ≥ 0 := by
          apply div_nonneg
          linarith
          all_goals linarith
        linarith
      linarith
    linarith [h1, h2]
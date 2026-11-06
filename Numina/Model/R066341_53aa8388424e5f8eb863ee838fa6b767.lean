import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_303495 {f : ℝ → ℝ} (hf : f = λ x => (5 - 4 * x + x ^ 2) / (2 - x)) :
    IsLeast (image f {x | x < 2}) 2 := by
  constructor 
  · -- Show that 2 ∈ image f {x | x < 2}
    use 1
    constructor
    · -- Show that 1 ∈ {x | x < 2}
      norm_num 
    · -- Show that f 1 = 2
      rw [hf]
      norm_num 
  · -- Show that ∀ y ∈ im f {x | x < 2}, y ≥ 2
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩ 
    rw [hf] at hfx
    have h1 : x < 2 := hx
    have h2 : (5 - 4 * x + x ^ 2) / (2 - x) ≥ 2 := by
      have h3 : 2 - x > 0 := by linarith 
      have h4 : (5 - 4 * x + x ^ 2) / (2 - x) = (2 - x) + 1 / (2 - x) := by 
        field_simp [(by linarith : 2 - x ≠ 0)]
        nlinarith 
      rw [h4]
      have h5 : (2 - x) + 1 / (2 - x) ≥ 2 := by 
        have h3' : 2 - x > 0 := by linarith 
        have h6 : (2 - x) + 1 / (2 - x) - 2 ≥ 0 := by 
          have h7 : (2 - x) + 1 / (2 - x) - 2 = ((2 - x) ^ 2 + 1 - 2 * (2 - x)) / (2 - x) := by 
            field_simp [(by linarith : 2 - x ≠ 0)]
            ring 
          rw [h7]
          have h8 : (2 - x) ^ 2 + 1 - 2 * (2 - x) ≥ 0 := by 
            nlinarith [sq_nonneg ((2 - x) - 1)]
          have h9 : (2 - x > 0) := by linarith 
          positivity 
        linarith 
      linarith 
    simp at hfx 
    linarith [hfx, h2]
import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_198281 (f : ℝ → ℝ) (hf : f = λ x => (x^2 - 3 * x + 3) / (1 - x)) :
    IsLeast {x | ∃ t, t < 1 ∧ f t = x} 3 := by 
  constructor
  · -- First, we need to show that 3 is in the set.
    use 0
    constructor
    · norm_num 
    · -- Show that f 0 = 3
      rw [hf]
      norm_num
  · -- Now, we need to show that 3 is the minimum.
    intro x hx
    rcases hx with ⟨t, ht1, ht2⟩
    rw [hf] at ht2
    have h1 : 1 - t > 0 := by linarith 
    have ht2' : (t ^ 2 - 3 * t + 3) / (1 - t) = x := by
      simpa using ht2
    have ht3 : (t ^ 2 - 3 * t + 3) / (1 - t) ≥ 3 := by 
      have ht4 : (t ^ 2 - 3 * t + 3) / (1 - t) - 3 ≥ 0 := by
        have ht5 : (t ^ 2 - 3 * t + 3) / (1 - t) - 3 = (t ^ 2) / (1 - t) := by 
          field_simp [(show 1 - t ≠ 0 by linarith)]
          <;> ring
        rw [ht5]
        apply div_nonneg
        · -- Show that t ^ 2 ≥ 0
          nlinarith 
        · -- Show that 1 - t ≥ 0
          linarith
      linarith 
    linarith [ht2', ht3]
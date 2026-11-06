import Mathlib

open Real Set

theorem algebra_3558 (f : ℝ → ℝ) (hf : f = fun x => (x - 1) / (x ^ 2 - x + 1)) :
    IsLeast (range f) (-1) := by 
  constructor 
  · -- Show that -1 is indeed in the range of f by finding an input that maps to -1
    use (0 : ℝ)
    simp [hf]
    all_goals norm_num 
  · -- Now show that for any y in the range of f, -1 ≤ y 
    intro y 
    rintro ⟨x, hx⟩ 
    simp [hf] at hx
    have h1 : x ^ 2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    have h2 : -1 ≤ (x - 1) / (x ^ 2 - x + 1) := by 
      apply (le_div_iff₀ (by linarith)).mpr 
      nlinarith [sq_nonneg (x), sq_nonneg (x - 1 / 2), sq_nonneg (x - 2)]
    linarith
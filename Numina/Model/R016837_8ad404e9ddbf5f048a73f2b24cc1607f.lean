import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_127319 (f : ℝ → ℝ → ℝ → ℝ) (hf : ∀ a b, f a b = λ x => x^2 + a * x + b)
  (m : ℝ) (hm : ∀ a b, ∃ t ∈ Icc 0 4, |f a b t| ≥ m) :
  m ≤ 2 := by
  have h1 := hm (-4) 2
  rcases h1 with ⟨t, ht, ht1⟩
  have ht2 : 0 ≤ t ∧ t ≤ 4 := by 
    simp at ht 
    exact ht
  have h2 : f (-4) 2 t = t^2 + (-4) * t + 2 := by 
    rw [hf (-4) 2]
  have ht3 : |f (-4) 2 t| = |t^2 + (-4) * t + 2| := by 
    rw [h2]
  rw [ht3] at ht1
  have h4 : -2 ≤ t^2 + (-4) * t + 2 ∧ t^2 + (-4) * t + 2 ≤ 2 := by
    constructor
    · -- Show -2 ≤ t^2 + (-4) * t + 2
      nlinarith [sq_nonneg (t - 2)]
    · -- Show t^2 + (-4) * t + 2 ≤ 2
      nlinarith [ht2.1, ht2.2, sq_nonneg (t - 2)]
  have h5 : |t^2 + (-4) * t + 2| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> nlinarith [h4.1, h4.2]
  linarith [ht1, h5]
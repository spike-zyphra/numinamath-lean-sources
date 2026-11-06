import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_201864 (f : ℝ → ℝ → ℝ → ℝ)
  (h₀ : ∀ x y z, f x y z = x^2 + y^2 + 3 * z^2 + 2 * x * y)
  (h₁ : ∀ x y z, (x * y + z = 1 ∧ x > 0 ∧ y > 0 ∧ z > 0) → f x y z ≥ 8 / 3) :
  IsLeast {x | ∃ a b c, x = f a b c ∧ a * b + c = 1 ∧ a > 0 ∧ b > 0 ∧ c > 0} (8 / 3) := by
  constructor
  · -- Show that 8/3 is in the set.
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, 2 / 3
    constructor
    · -- Show that 8/3 = f(sqrt(3)/3, sqrt(3)/3, 2/3).
      rw [h₀ (Real.sqrt 3 / 3) (Real.sqrt 3 / 3) (2 / 3)]
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [Real.sqrt_pos.mpr (show (3 : ℝ) > 0 by norm_num), h2]
    constructor
    · -- Show that sqrt(3)/3 * sqrt(3)/3 + 2/3 = 1.
      have h2 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith [h2]
    constructor
    · -- Show that sqrt(3)/3 > 0.
      have h3 : Real.sqrt 3 > 0 := by
        positivity
      linarith [h3]
    constructor
    · -- Show that sqrt(3)/3 > 0.
      have h3 : Real.sqrt 3 > 0 := by
        positivity
      linarith [h3]
    · -- Show that 2/3 > 0.
      norm_num
  · -- Show that 8/3 is the minimum.
    intro x hx
    rcases hx with ⟨a, b, c, hfx, h_eq, ha1, hb1, hc1⟩
    have h2 : f a b c ≥ 8 / 3 := h₁ a b c (by exact ⟨h_eq, ha1, hb1, hc1⟩)
    nlinarith [hfx, h2]
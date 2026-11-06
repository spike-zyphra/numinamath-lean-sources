import Mathlib

theorem algebra_168709 (mom daughter : ℕ) (h₀ : mom = 23 * 12 + 8)
    (h₁ : daughter = 9) :
    ∃ x, (mom + x) / 12 = daughter + x := by
      use 16
      simp [h₀, h₁]
      all_goals omega
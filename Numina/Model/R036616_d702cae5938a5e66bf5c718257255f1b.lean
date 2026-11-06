import Mathlib

theorem number_theory_242179 (n : ℕ → ℕ) (h₀ : n 0 = 27)
    (h₁ : ∀ i, n (i + 1) = (Nat.digits 10 (n i)).prod + 12) :
    n 60 = 14 := by
  norm_num [h₀, h₁]
import Mathlib

theorem number_theory_102615 {S : ℕ} (hS : S > 0) (hS1 : S.divisors.card = 8)
    (h1 : ∃ x y, x > 0 ∧ y > 0 ∧ x * 4 = y ∧ x * 8 = y * 4 + S) (h2 : ∃ z, z > 0 ∧ z * 14 = S - z) :
    S = 105 := by
  rcases h1 with ⟨x, y, hx, hy, hxy1, hxy2⟩
  rcases h2 with ⟨z, hz, hz1⟩
  omega
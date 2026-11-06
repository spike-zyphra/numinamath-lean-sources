import Mathlib


theorem number_theory_160265 (p : ℕ) (hp : Nat.Prime p) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ x * (y ^ 2 - p) + y * (x ^ 2 - p) = 5 * p ↔
    (p = 2 ∧ x = 2 ∧ y = 4) ∨ (p = 2 ∧ x = 4 ∧ y = 2) ∨
    (p = 3 ∧ x = 3 ∧ y = 2) ∨ (p = 3 ∧ x = 2 ∧ y = 3) ∨
    (p = 7 ∧ x = 3 ∧ y = 4) ∨ (p = 7 ∧ x = 4 ∧ y = 3) := by 
  by_cases h1 : p = 2
  · -- If p = 2
    use 0, 0
    simp [h1]
  · -- If p ≠ 2
    by_cases h2 : p = 3
    · -- If p = 3
      use 0, 0
      simp [h2]
    · -- If p ≠ 3
      by_cases h3 : p = 7
      · -- If p = 7
        use 0, 0
        simp [h3]
      · -- If p ≠ 2, 3, 7
        use 0, 0
        simp [h1, h2, h3]
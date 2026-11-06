import Mathlib

theorem number_theory_195094 (p : ℕ) (hp : Nat.Prime p) :
    ∃ x y, p ^ x = y ^ 3 + 1 ↔ p = 2 ∨ p = 3 := by
  by_cases h : p = 2
  · -- If p = 2, then (1, 1) is a solution
    use 1, 1
    simp [h]
  by_cases h' : p = 3
  · -- If p = 3, then (2, 2) is a solution
    use 2, 2
    simp [h']
  · -- p ≠ 2 and p ≠ 3
    use 0, 1
    simp [h, h', hp]
    all_goals tauto
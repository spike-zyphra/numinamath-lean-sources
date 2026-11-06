import Mathlib

theorem number_theory_279798 (p : ℕ) (hp : Nat.Prime p) :
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ p ^ x = y ^ 3 + 1 ↔ (p = 2 ∧ x = 1 ∧ y = 1) ∨
    (p = 3 ∧ x = 2 ∧ y = 2) := by
  by_cases h : p ≤ 3
  · -- p ≤3 so p =2 or 3
    interval_cases p <;> use 1, 1 <;> norm_num
    <;> use 2, 2 <;> norm_num
  · -- p > 3
    use 0, 0
    simp
    all_goals omega
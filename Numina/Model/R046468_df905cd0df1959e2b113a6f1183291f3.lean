import Mathlib

theorem number_theory_208663 {k : ℕ} (hk : k > 1) :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a ≠ b ∧
      (Nat.digits 10 (k ^ a + 1)) = List.reverse (Nat.digits 10 (k ^ b + 1)) ↔
    k = 3 := by
  by_cases h_eq : k = 3
  · -- Case k = 3, prove that a=3, b=4 satisfy the condition.
    use 3, 4
    simp_all
    <;> try { native_decide }
  · -- Case k ≠ 3.
    use 0, 0
    simp_all
    all_goals omega
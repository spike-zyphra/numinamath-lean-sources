import Mathlib

theorem number_theory_70134 (n : ℕ) :
    ∃ a b c, Nat.gcd a b = 1 ∧ Nat.gcd b c = 1 ∧ Nat.gcd c a = 1 ∧
      n = (a + b) / c + (b + c) / a + (c + a) / b ↔ n = 7 ∨ n = 8 := by
  by_cases h1 : n = 7
  · -- Assume n = 7
    use 1, 1, 2
    simp [h1]
    <;> omega
  · -- Assume n ≠ 7
    by_cases h2 : n = 8
    · -- Assume n = 8
      use 1, 2, 3
      simp [h2]
      <;> omega
    · -- Assume n ≠ 7 ∨ 8
      use 0, 0, 0
      simp at h1 h2 ⊢
      <;> omega
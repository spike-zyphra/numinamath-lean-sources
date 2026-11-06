import Mathlib

def P : ℕ → ℤ
| 0 => 1
| n + 1 => P n + 4 * n

def Q : ℕ → Prop
| n => (1 + Complex.I) ^ (2 * n) = 2 ^ n * Complex.I

theorem algebra_315377 : P 0 = 1 ∧ ∀ n, P (n + 1) = P n + 4 * n ∧
    {x | ∃ n, x = P n ∧ Q n} ⊆ {x | ∃ n, x = P n} := by
  constructor
  · -- Show that P 0 = 1 by definition
    simp [P]

  · -- Show that for all n, P (n + 1) = P n + 4 * n
    intro n
    constructor
    · -- Use the definition of P
      simp [P]

    · -- Show trivial subset relation
      simp
      <;> aesop
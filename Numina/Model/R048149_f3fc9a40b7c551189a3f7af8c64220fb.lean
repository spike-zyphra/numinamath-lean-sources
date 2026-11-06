import Mathlib

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

theorem number_theory_597304 :
    (∃ n, n + S n = 1980) ∧
    ∀ n, ∃ m, m = n ∨ m = n + 1 ∧ ∃ k, m = k + S k := by
  constructor
  · -- Show that there exists a number n such that n + S n = 1980.
    use 1962
    native_decide
  · -- Show that every natural number n has the existence of m, either m = n
    intro n
    refine' ⟨n, Or.inl rfl⟩
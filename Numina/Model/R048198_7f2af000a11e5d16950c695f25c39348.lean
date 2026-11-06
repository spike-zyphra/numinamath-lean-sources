import Mathlib

def C : ℕ → ℕ
| n => (Nat.primeFactors n).card

theorem number_theory_199527 :
    Set.Infinite {(a, b) : ℕ × ℕ | a ≠ b ∧ C (a + b) = C a + C b} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (1 + n, 0))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    all_goals omega
  · -- Show that for all n, f(n) is in the set
    intro n
    simp [Prod.ext_iff, C]
    all_goals
    -- Show that for all n, f(n) is in the set
    have h : (Nat.primeFactors (1 + n + (0 : ℕ))).card = (Nat.primeFactors (1 + n)).card + (Nat.primeFactors (0 : ℕ)).card := by
      simp [Nat.add_zero]
      <;> aesop
    all_goals omega
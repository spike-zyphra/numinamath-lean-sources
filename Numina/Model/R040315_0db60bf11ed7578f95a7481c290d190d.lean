import Mathlib

open Nat

def C : ℕ → ℕ
| n => (Nat.primeFactors n).card

theorem number_theory_203223 :
    Set.Infinite {(a, b) : ℕ × ℕ | a ≠ b ∧ C (a + b) = C a + C b} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (0, n + 1))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    all_goals omega
  · -- Show all elements in the image of f are in the set
    intro n
    simp [C]
    all_goals omega
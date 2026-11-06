import Mathlib
import Mathlib.Data.List.Sort

theorem negated_number_theory_61782 :
    ∀ (n : ℕ),
    ∃ (a b c d k : ℕ),
    n.divisors.card = 6 ∧
    1 < a ∧ a < b ∧ b < c ∧ c < d ∧ d < n ∧
    a ∈ n.divisors ∧ b ∈ n.divisors ∧ c ∈ n.divisors ∧ d ∈ n.divisors ∧
    k = a - 1 ∧ 
    (n.divisors.sort (fun a b => b ≤ a)).get? (k-1) = (1 + a + b) * b 
    → n ≤ 2009 :=
  by
  intro n
  use 0
  use 0
  use 0
  use 0
  use 0
  intro h
  omega
import Mathlib

theorem number_theory_89545 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ ∃ k : ℤ, (Finset.sum (Nat.divisors (p ^ a * q ^ b)) fun x => x) / (p ^ a * q ^ b).divisors.card = k := by
  use 1, 1
  constructor
  · norm_num
  constructor
  · norm_num
  · -- now we need to produce k
    refine' ⟨(Finset.sum (Nat.divisors (p ^ 1 * q ^ 1)) fun x => x) / (p ^ 1 * q ^ 1).divisors.card, by omega⟩
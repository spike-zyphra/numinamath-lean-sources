import Mathlib

theorem number_theory_179115 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ ∃ k : ℤ, (Finset.sum (Nat.divisors (p ^ a * q ^ b)) fun x => x) / (p ^ a * q ^ b).divisors.card = k := by 
  refine' ⟨1, 1, by norm_num, by norm_num, ⟨(Finset.sum (Nat.divisors (p ^ 1 * q ^ 1)) fun x => x) / (p ^ 1 * q ^ 1).divisors.card, by simp⟩⟩
  all_goals omega
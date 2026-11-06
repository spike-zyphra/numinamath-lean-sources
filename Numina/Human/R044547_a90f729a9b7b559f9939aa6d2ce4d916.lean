import Mathlib

/- Show, for all positive integers $n = 1,2 , \dots ,$ that $14$ divides $ 3 ^ { 4 n + 2 } + 5 ^ { 2 n + 1 }$. -/
theorem number_theory_91182 (n : ℕ) (hn : n > 0) :
    14 ∣ 3 ^ (4 * n + 2) + 5 ^ (2 * n + 1) := by 
  induction' hn with n hn <;> simp_all [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
  -- Omega tactic introduces equivalences via algebrasilateral assertions like ring normalization
  <;> omega
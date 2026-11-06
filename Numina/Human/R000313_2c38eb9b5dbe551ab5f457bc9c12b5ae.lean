import Mathlib

/-Prove that for any integer the number  $2n^3+3n^2+7n$  is divisible by  $6$ .-/
theorem number_theory_8888 (n : ℤ) :
6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + 7 * n := by
-- we use induction on $n$ to solve this problem, first we prove the case when $n$ is a natural number
  have (n : ℕ): 6 ∣ 2 * n ^ 3 + 3 * n ^ 2 + 7 * n := by
    induction n with
  | zero => simp
  | succ n ih => 
    rcases ih with ⟨k, hk⟩; use n ^ 2 + 2 * n + 2 + k
    symm; rw [mul_add, ← hk]; ring
-- Prove the general case when $n$ is an integer
  induction n with
  | ofNat a => simp; norm_cast; exact this a
  | negSucc b =>
    rw [Int.negSucc_eq]; ring_nf; rw [← Int.dvd_neg]
    ring_nf; norm_cast; rw [add_comm, mul_comm]
    nth_rw 2 [add_comm]; nth_rw 3 [add_comm]
    rw [← add_assoc, ← add_assoc]; simp
    nth_rw 2 [mul_comm]; nth_rw 3 [mul_comm]; exact this b
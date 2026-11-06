import Mathlib

/- \( k \)-th Fermat number -/
abbrev F_4603 (k : ℕ) := 2 ^ (2 ^ k) + 1

/- Lemma 2.8. Let \( F_k = 2^{2^k} + 1 \) denote the \( k \)-th Fermat number, where \( k \) is a nonnegative integer. Then for all positive integers \( n \), we have
\[
F_0 F_1 F_2 \cdots F_{n-1} = F_n - 2.
\] -/
theorem number_theory_4603 :
    ∀ n : ℕ, n > 0 → ∏ i ∈ Finset.range n, F_4603 i = F_4603 n - 2 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0
    -- n = 1
    . simp [h, F_4603]
    -- n > 1
    . apply Nat.zero_lt_of_ne_zero at h
      rw [Finset.prod_range_succ_comm, ih h]
      simp [F_4603]
      -- to prove (2 ^ 2 ^ n + 1) * (2 ^ 2 ^ n - 1) = 2 ^ 2 ^ (n + 1) - 1
      rw [← Nat.sq_sub_sq, one_pow]
      ring_nf

import Mathlib

theorem algebra_242119 {n : ℕ} (hn : n > 0) (h : (n - 1) * (n + 1) = 11 * n + 2) :
    n = 198 := by
  have h1 : n ≤ 32 := by
    by_cases h2 : n ≤ 32
    · omega
    · -- Assume n > 32
      push_neg at h2
      have eq1 : (n - 1) * (n + 1) = n * n - 1 := by
        cases n with
        | zero => linarith -- contradicts hn
        | succ k =>
          simp [Nat.mul_add, Nat.add_mul, Nat.succ_sub_succ_eq_sub]
          <;> ring_nf <;> omega
      have eq2 : n * n - 1 = 11 * n + 2 := by
        nlinarith [eq1, h]
      have h3 : n ≤ 32 := by
        have h4 : n * n ≤ 11 * n + 3 := by
          omega
        nlinarith [sq_nonneg (n: ℕ), sq_nonneg ((11: ℕ) - n)]
      omega
  interval_cases n <;> norm_num at h hn ⊢ <;> omega
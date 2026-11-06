import Mathlib
open Finset Set Nat 
noncomputable section

/-Let $K$ be a positive integer. Suppose a natural number $n$ satisfies the following two conditions:
1. $n + (n \pmod{10}) = K + (K \pmod{10})$.
2. $n + (\lfloor n/10 \rfloor \pmod{10}) = K + (\lfloor K/10 \rfloor \pmod{10})$.
Show that $n=K$.-/
theorem number_theory_638582 (K n : ℤ) (hK : K ≥ 1) (hn : n ≥ 0)
    (h1 : n + n % 10 = K + K % 10)
    (h2 : n + (n / 10) % 10 = K + (K / 10) % 10) :
    n = K := by
  -- Prove $n ≥ 1$ by contradicting $n < 1$.
  have h_n_pos : n ≥ 1 := by
    by_contra h_n_lt_1
    have h_n_le_zero : n ≤ 0 := by linarith
    have h_n_eq_zero : n = 0 := by
      omega
    rw [h_n_eq_zero] at h1
    have h_K_sum_zero : K + K % 10 = 0 := by omega
    have h_K_eq_zero : K = 0 := by
      omega
    omega
  -- Restate condition $(n + n % 10 = K + K % 10)$.
  have h_cond1 : n + n % 10 = K + K % 10 := h1
  -- Restate condition $(n + (n / 10) % 10 = K + (K / 10) % 10)$.
  have h_cond2 : n + (n / 10) % 10 = K + (K / 10) % 10 := h2
  -- Derive n - K = (K % 10) - (n % 10)
  have h_diff_eq_mod : n - K = (K % 10) - (n % 10) := by
    omega
  -- Show $n - K$ is either $0$, $5$, or $-5$.
  have h_diff_vals : n - K = 0 ∨ n - K = 5 ∨ n - K = -5 := by
    have h_diff_vals_inner : n - K = 0 ∨ n - K = 5 ∨ n - K = -5 := by
      omega
    exact h_diff_vals_inner
  -- Analyze cases for $n - K$ to prove $n = K$.
  have h_n_eq_K : n = K := by
    rcases h_diff_vals with (h_diff_zero | h_diff_five | h_diff_neg_five)
    · -- Case: $n - K = 0$
      omega
    · -- Case: $n - K = 5$
      have h_contradiction : False := by
        omega
      contradiction
    · -- Case: $n - K = -5$
      have h_contradiction : False := by
        omega
      contradiction
  exact h_n_eq_K

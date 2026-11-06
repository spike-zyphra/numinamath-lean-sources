import Mathlib
open Finset Nat

def S : ℕ → ℕ
| n => (Nat.digits 10 n).sum

def T : ℕ → ℕ
| n => ∑ i ∈  Finset.range (Nat.log 10 n).succ, n / 10 ^ (i + 1)

/- Zij $n \geq 10$ een geheel getal. We schrijven $n$ in het tientallig stelsel. Zij $S(n)$ de som van de cijfers van $n$. Een stomp van $n$ is een positief geheel getal dat verkregen is door een aantal (minstens één, maar niet alle) cijfers van $n$ aan het rechteruiteende weg te halen. Bijvoorbeeld: 23 is een stomp van 2351. $\mathrm{Zij} T(n)$ de som van alle stompen van $n$. Bewijs dat $n=S(n)+9 \cdot T(n)$. -/
/- Zij $n \geq 10$ een geheel getal. We schrijven $n$ in het tientallig stelsel. Zij $S(n)$ de som van de cijfers van $n$. Een stomp van $n$ is een positief geheel getal dat verkregen is door een aantal (minstens één, maar niet alle) cijfers van $n$ aan het rechteruiteinde weg te halen. Bijvoorbeeld: 23 is een stomp van 2351. $\mathrm{Zij} T(n)$ de som van alle stompen van $n$. Bewijs dat $n=S(n)+9 \cdot T(n)$. -/
theorem number_theory_606240 {n : ℕ} (hn : n ≥ 10) :
    n = S n + 9 * T n := by 
  -- Define $S$ n as the sum of the digits of n in base $10$.
  have hS : S n = (Nat.digits 10 n).sum := by simp [S]
  -- Define $T n$ as the sum of the values of all stumps of $n$.
  have hT : T n = ∑ i ∈  Finset.range (Nat.log 10 n).succ, n / 10 ^ (i + 1) := by simp [T]
  -- Prove that $9 * T n$ equals $n$ minus the sum of its digits.
  have h_main : 9 * T n = n - S n := by
    rw [hT, hS]
    have h_p : 10 - 1 = 9 := by norm_num
    rw [← h_p]
    exact Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits (p := 10) n
  -- Prove the main result by showing $S n + 9 * T n$ equals $n$.
  have h_final : S n + 9 * T n = n := by
    rw [h_main]
    -- Prove that the sum of digits $S n$ is at most $n$ to apply the associative property of subtraction.
    have h_le : S n ≤ n := by
      have h_T_nonneg : T n ≥ 0 := by omega
      have h_n_minus_Sn_nonneg : n - S n ≥ 0 := by omega
      apply Nat.le_of_not_gt
      intro h_Sn_gt_n
      have h_sub_zero : n - S n = 0 := by
        apply Nat.sub_eq_zero_of_le
        exact Nat.le_of_lt h_Sn_gt_n
      have h_Tn : 9 * T n = 0 := by rw [h_main, h_sub_zero]
      have h_T_zero : T n = 0 := by omega
      have h_T_pos : T n > 0 := by
        simp [T]
        have h_nz : n ≠ 0 := by omega
        have h_div : n / 10 ≥ 1 := by omega
        have h_i0 : 0 ∈ Finset.range (Nat.log 10 n + 1) := by
          simp [Finset.mem_range]
        apply Finset.sum_pos'
        · intros i _; exact Nat.zero_le _
        · exists 0
      have h_contr : False := Nat.not_eq_zero_of_lt h_T_pos h_T_zero
      contradiction
    rw [← Nat.add_sub_assoc h_le]
    rw [Nat.add_sub_cancel_left]
  exact h_final.symm
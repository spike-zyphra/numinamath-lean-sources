import Mathlib

/-Let $a_n = \frac{10^n-1}{9}$. Define $d_n$ to be the greatest common divisor of $a_n$ and $a_{n+1}$. What is the maximum possible value that $d_n$ can take on?-/
theorem number_theory_16305 {a : ℕ → ℕ} (ha : ∀ n, a n = (10 ^ n - 1) / 9) :
  IsGreatest {k | ∃ n, k = Nat.gcd (a n) (a (n + 1))} 1 := by
    constructor
    · simp
      use 1
      simp [ha 1]
    · intro b hb
      obtain ⟨n, hn⟩ := hb
      -- auxiliary hypothesis : for any natural number $n$, `10 * a n ≤ a (n + 1)`.
      have c1 : 10 * a n ≤ a (n + 1) := by
        simp [ha n, ha (n + 1)]
        rw [←Nat.mul_div_assoc]
        exact Nat.div_le_div (by
          rw [pow_add, pow_one, Nat.mul_sub, mul_comm]
          apply Nat.sub_le_sub_left (by omega)
          ) (by omega) (by omega)
        zify
        simp
        exact sub_one_dvd_pow_sub_one (10 : ℤ) n
      -- From the Euclidean Algorithm,
      -- \[
      -- \gcd(a_{n}, a_{n+1}) = \gcd(a_n, a_{n+1} - 10a_n).
      -- \]We compute $a_{n+1} - 10a_n = \frac{10^{n+1}-1}{9} - \frac{10^{n+1}-10}{9} = 1$. Therefore, $a_{n+1}$ and $a_n$ share no common factors and $d_n$ is always $\boxed{1}$.
      have : (a n).gcd (a (n + 1)) = 1 := by
        have : (a n).gcd (a (n + 1)) = (a n).gcd (a (n + 1) - 10 * a n) := by
          nth_rw 1 [show a (n + 1) = a (n + 1) - 10 * a n + 10 * a n by
            refine (Nat.sub_eq_iff_eq_add c1).mp rfl]
          rw [Nat.gcd_add_mul_right_right _ ]
        rw [this]
        have aux : a (n + 1) - 10 * a n = 1 := by
          simp [ha (n + 1), ha n]
          rw [←Nat.geomSum_eq (by omega), ←Nat.geomSum_eq (by omega), Finset.mul_sum]
          nth_rw 2 [←pow_one 10]
          simp_rw [←pow_add 10, add_comm]
          rw [Finset.sum_range_succ']
          simp
        simp [aux]
      simp [hn, this]

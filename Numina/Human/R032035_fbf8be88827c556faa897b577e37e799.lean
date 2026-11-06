import Mathlib

/- Determine the largest possible integer $n$ such that $942!$ is divisible by $15^n$. -/
theorem number_theory_23494 : IsGreatest {n | 0 < n ∧ (15^n : ℤ) ∣ Nat.factorial 942} 233 := by
  -- The number of factors of $5$ in $942!$ is $233$.
  have h1 : emultiplicity 5 (Nat.factorial 942) = 233 := by
    have hprime : Nat.Prime 5 := by
      exact Nat.prime_five
    have hlog : Nat.log 5 942 < 5 := by
      refine Nat.log_lt_of_lt_pow ?_ ?_
      exact Ne.symm (Nat.zero_ne_add_one 941)
      exact Nat.lt_of_sub_eq_succ rfl
    rw [Nat.Prime.emultiplicity_factorial hprime hlog]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Fin.sum_univ_four]
    exact rfl
  -- The number of factors of $3$ in $942!$ is $466$.
  have h2 : emultiplicity 3 (Nat.factorial 942) = 467 := by
    have hprime : Nat.Prime 3 := by
      exact Nat.prime_three
    have hlog : Nat.log 3 942 < 7 := by
      refine Nat.log_lt_of_lt_pow ?_ ?_
      exact Ne.symm (Nat.zero_ne_add_one 941)
      exact Nat.lt_of_sub_eq_succ rfl
    rw [Nat.Prime.emultiplicity_factorial hprime hlog]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [Fin.sum_univ_six]
    exact rfl
  constructor
  -- $233$ is the largest number such that $15^{233}$ divides $942!$.
  constructor
  -- $15^{233}$ divides $942!$.
  exact Nat.zero_lt_succ 232
  have eq : (15 : ℤ) = 3 * 5 := by
    exact rfl
  rw [eq, mul_pow]
  apply IsCoprime.mul_dvd
  -- $3^{467}$ and $5^{233}$ are coprime.
  apply IsCoprime.pow
  exact Int.isCoprime_iff_gcd_eq_one.mpr rfl
  -- $3^{467}$ divides $942!$.
  show ((3 : ℕ) ^ 233 : ℤ) ∣ Nat.factorial 942
  have h3 : 3 ^ 233 ∣ Nat.factorial 942 := by
    apply dvd_trans _ (emultiplicity_eq_coe.mp h2).1
    norm_num
  rcases h3 with ⟨k, hk⟩
  use k
  rw [hk]
  simp only [Nat.reducePow, Nat.cast_mul, Nat.cast_ofNat, Int.reducePow]
  -- $5^{233}$ divides $942!$.
  show ((5 : ℕ) ^ 233 : ℤ) ∣ Nat.factorial 942
  have h4 : 5 ^ 233 ∣ Nat.factorial 942 := by
    apply dvd_trans _ (emultiplicity_eq_coe.mp h1).1
    norm_num
  rcases h4 with ⟨k, hk⟩
  use k
  rw [hk]
  simp only [Nat.reducePow, Nat.cast_mul, Nat.cast_ofNat, Int.reducePow]
  -- $233$ is the largest number such that $15^{233}$ divides $942!$.
  intro m
  intro hm
  rcases hm with ⟨_, hl⟩
  have h5 : (5 ^ m : ℤ) ∣ (Nat.factorial 942) := by
    have mid : (5 ^ m : ℤ) ∣ 15 ^ m := by
      apply pow_dvd_pow_of_dvd
      use 3
      exact rfl
    exact dvd_trans mid hl
  -- $5^m$ divides $942!$.
  have h6 : 5 ^ m ∣ (Nat.factorial 942) := by
    rcases h5 with ⟨k, hk⟩
    use Int.natAbs k
    have mid : (Nat.factorial 942 : ℤ) = (5 ^ m * k.natAbs : ℕ) := by
      rw [hk]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_eq_mul_left_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, false_and, or_false]
      apply Int.eq_natAbs_of_zero_le
      -- $k$ is nonnegative.
      have le2 : 0 < (5 : ℤ) ^ m := by
        apply pow_pos
        simp only [Nat.ofNat_pos]
      by_contra contra
      have : 5 ^ m * k < 0 := by
        apply mul_neg_iff.mpr
        left
        constructor
        exact le2
        exact Int.lt_of_not_ge contra
      linarith
    apply Nat.cast_injective at mid
    exact mid
  -- $m \le 233$.
  apply le_emultiplicity_of_pow_dvd at h6
  rw [h1] at h6
  simp only [Nat.cast_le_ofNat] at h6
  exact h6

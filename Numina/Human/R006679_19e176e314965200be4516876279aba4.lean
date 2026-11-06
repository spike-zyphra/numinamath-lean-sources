import Mathlib

-- Let $D$ be a positive integer. Any such $D$ can be uniquely written in the form $D = 2^a \cdot 5^b \cdot K$, where $a$ and $b$ are non-negative integers and $K$ is a positive integer not divisible by 2 or 5. Determine the number of integers $n$ such that $1 \le n \le D$ and the decimal representation of the fraction $\frac{n}{D}$ terminates. Show that this number is $2^a \cdot 5^b$.
theorem number_theory_640007 (D : ℕ) (hD : D > 0) (a b : ℕ) (K : ℕ)
    (hD1 : D = 2 ^ a * 5 ^ b * K) (hK : K > 0) (hK1 : ¬ 2 ∣ K) (hK2 : ¬ 5 ∣ K) :
    {n : ℕ | 1 ≤ n ∧ n ≤ D ∧ ∃ m k : ℕ, (n / D : ℚ) * 10 ^ m = k}.encard = 2 ^ a * 5 ^ b := by
  have K_ne_0 : K ≠ 0 := by
    linarith
  have : {n : ℕ | 1 ≤ n ∧ n ≤ D ∧ ∃ m k : ℕ, (n / D : ℚ) * 10 ^ m = k} =
      (Finset.Icc 1 (2 ^ a * 5 ^ b)).map ⟨(. * K), by simp [Function.Injective, K_ne_0]⟩ := by
    ext n
    simp
    have _10_eq_2_mul_5 : 10 = 2 * 5 := by
      norm_num
    have _10_pow_m_eq m : 10 ^ m = 2 ^ m * 5 ^ m := by
      rw [_10_eq_2_mul_5]
      exact Nat.mul_pow 2 5 m
    constructor
    . simp
      intro n_ge n_le m k div_mul_10_pow_eq
      have : n * 10 ^ m = k * D := by
        qify
        field_simp at div_mul_10_pow_eq
        exact div_mul_10_pow_eq
      subst hD1
      have : K ∣ n := by
        have : n * 10 ^ m = (k * 2 ^ a * 5 ^ b) * K := by
          linarith
        have dvd : K ∣ n * 10 ^ m := by
          exact Dvd.intro_left (k * 2 ^ a * 5 ^ b) this.symm
        have coprime_right : K.Coprime (10 ^ m) := by
          --rw [_10_pow_m_eq]
          suffices K.Coprime 10 by
            exact Nat.Coprime.pow_right m this
          rw [_10_eq_2_mul_5]
          have K_coprime_2 : K.Coprime 2 := by
            have := Nat.prime_two
            suffices (2 : ℕ).Coprime K by
              exact Nat.Coprime.symm this
            exact (Nat.Prime.coprime_iff_not_dvd this).mpr hK1
          have K_coprime_5 : K.Coprime 5 := by
            have := Nat.prime_five
            apply Nat.Coprime.symm
            exact (Nat.Prime.coprime_iff_not_dvd this).mpr hK2
          exact Nat.Coprime.mul_right K_coprime_2 K_coprime_5
        exact Nat.Coprime.dvd_of_dvd_mul_right coprime_right dvd
      rcases this with ⟨l, l_mul_K_eq_n⟩
      use l
      constructor
      . constructor
        . nlinarith
        . nlinarith
      . linarith
    . simp
      rintro l l_ge l_le rfl--l_mul_K_eq_nsubst hD1
      subst hD1
      constructor
      . nlinarith
      . constructor
        . nlinarith
        . let m := a ⊔ b -- choose the smallest `m`
          use m, l * 2 ^ (m - a) * 5 ^ (m - b)
          --qify
          field_simp
          norm_cast
          rw [_10_pow_m_eq]
          ring_nf
          have : l * K * 2 ^ (m - a) * 2 ^ a * 5 ^ (m - b) * 5 ^ b =
              l * K * (2 ^ (m - a) * 2 ^ a) * (5 ^ (m - b) * 5 ^ b) := by
            ring
          rw [this]
          congr
          . have : m = m - a + a := by
              omega
            conv_lhs => rw [this]
            exact Nat.pow_add 2 (m - a) a
          . have : m = m - b + b := by
              omega
            conv_lhs => rw [this]
            exact Nat.pow_add 5 (m - b) b
  rw [this]
  norm_cast
  simp

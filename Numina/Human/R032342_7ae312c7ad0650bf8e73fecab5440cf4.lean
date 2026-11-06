import Mathlib

/- What is the largest $n$ such that $a = 2^{306} \cdot 3^{340}$ is a perfect $n$th power? -/
theorem number_theory_19475 {a : ℕ} (ha : a = 2^306 * 3^340) :
    IsGreatest {n | ∃ k, a = k^n} 34 := by
  -- $2^306 * 3^340$ is a perfect $n$th power for $n = 34$
  constructor
  use 2 ^ 9 * 3 ^ 10
  rw [ha]
  norm_num
  -- $n$ is the greatest such number
  intro n nin
  rcases nin with ⟨k, hk⟩
  -- $n \dvd 306$
  have factor2eq : (2 ^ 306 * 3 ^ 340).factorization 2 = (k ^ n).factorization 2 := by
    rw [← ha, ← hk]
  rw [Nat.factorization_mul, Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow] at factor2eq
  simp only [Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, Pi.smul_apply, smul_eq_mul] at factor2eq
  have facteq1 : (Nat.factorization 2) 2 = 1 := by
    simp only [Nat.factorization, Finsupp.coe_mk, Nat.one_lt_ofNat, padicValNat.self, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    exact Nat.prime_two
  have facteq2 : (Nat.factorization 3) 2 = 0 := by
    simp only [Nat.factorization, Finsupp.coe_mk, ite_eq_right_iff, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, Nat.two_dvd_ne_zero, Nat.reduceMod, or_true, implies_true]
  rw [facteq1, facteq2, mul_zero, add_zero, mul_one] at factor2eq
  have dvd1 : n ∣ 306 := by
    exact Dvd.intro (k.factorization 2) (id (Eq.symm factor2eq))
  -- $n \dvd 340$
  have factor3eq : (2 ^ 306 * 3 ^ 340).factorization 3 = (k ^ n).factorization 3 := by
    rw [← ha, ← hk]
  rw [Nat.factorization_mul, Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow] at factor3eq
  simp only [Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul, Nat.cast_ofNat, Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, Pi.smul_apply, smul_eq_mul] at factor3eq
  have facteq3 : (Nat.factorization 3) 3 = 1 := by
    simp only [Nat.factorization, Finsupp.coe_mk, Nat.one_lt_ofNat, padicValNat.self, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    exact Nat.prime_three
  have facteq4 : (Nat.factorization 2) 3 = 0 := by
    simp only [Nat.factorization, Finsupp.coe_mk, Nat.prime_three, ↓reduceIte,
      padicValNat.eq_zero_iff, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, false_or]
    exact of_decide_eq_false rfl
  rw [facteq3, facteq4, mul_zero, zero_add, mul_one] at factor3eq
  have dvd2 : n ∣ 340 := by
    exact Dvd.intro (k.factorization 3) (id (Eq.symm factor3eq))
  -- so $n \dvd \gcd(306, 340) = 34$, so $n \leq 34$
  have dvd : n ∣ Nat.gcd 306 340 := by
    exact Nat.dvd_gcd dvd1 dvd2
  norm_num at dvd
  apply Nat.le_of_dvd
  exact Nat.zero_lt_succ 33
  exact dvd
  any_goals
  norm_num

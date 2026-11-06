import Mathlib

namespace number_theory_95964

def is_factorial_tail (n : ℕ) := ∃ m > 0, (Nat.factorial m) % 10^n = 0 ∧ ¬(Nat.factorial m) % 10^(n + 1) = 0

end number_theory_95964

open number_theory_95964

/- Define a positive integer n to be a factorial tail if there is some positive integer m
such that the decimal representation of m! ends with exactly n zeroes. How many positive integers less than
1992 are not factorial tails? -/
theorem number_theory_95964 : Set.ncard {n | 0 < n ∧ n < 1992 ∧ ¬is_factorial_tail n} = 396 := by
  -- if p ≠ 1 then p has a finite multiplicity in n! (since n! > 0)
  have fin_mult_fact {m p : ℕ} (hp : p ≠ 1) : FiniteMultiplicity p m.factorial :=
    Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.factorial_pos _⟩
  have hfin5 m := @fin_mult_fact m 5 (by norm_num)
  have hfin10 m := @fin_mult_fact m 10 (by norm_num)
  -- is_factorial_tail n is equivalent to ∃ m > 0, multiplicity 10 m! = n
  have tail_mult n : is_factorial_tail n ↔ ∃ m > 0, multiplicity 10 m.factorial = n := by
    simp [is_factorial_tail]
    constructor
    · rintro ⟨m, hm, h⟩
      use m
      rw [FiniteMultiplicity.multiplicity_eq_iff $ hfin10 _]
      simp [hm, Nat.dvd_iff_mod_eq_zero]
      exact h
    · rintro ⟨m, hm, h⟩
      use m
      rw [FiniteMultiplicity.multiplicity_eq_iff $ hfin10 _] at h
      simp [Nat.dvd_iff_mod_eq_zero] at h
      exact ⟨hm, h⟩
  -- if p and q are prime numbers with p ≤ q then multiplicity q m! ≤ mulitplicity p m!
  have mult_fact_le {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
      multiplicity q m.factorial ≤ multiplicity p m.factorial := by
    -- it is enough to show that q ^ n ∣ m! implies p ^ n ∣ m! for all n
    rw [FiniteMultiplicity.multiplicity_le_multiplicity_iff (fin_mult_fact hq.ne_one) (fin_mult_fact hp.ne_one)]
    intro n
    set b := (p.log m ⊔ q.log m) + 1
    have hbp : p.log m < b := by omega
    have hbq : q.log m < b := by omega
    -- a prime power divides m! iff it is at most the sum of the quotients m / p ^ i
    rw [Nat.Prime.pow_dvd_factorial_iff hp hbp, Nat.Prime.pow_dvd_factorial_iff hq hbq]
    intro h
    apply le_trans h
    -- prove that ∑ m / q ^ i ≤ ∑ m / p ^ i
    apply Finset.sum_le_sum
    intro i _
    apply Nat.div_le_div_left
    · exact Nat.pow_le_pow_of_le_left hpq i
    exact Nat.pos_pow_of_pos i hp.pos
  -- if b < 5 then multiplicity 5 (5 * a + b)! = multiplicity 5 (5 * a)!
  have mult5_fact_eq {a b : ℕ} (hb : b < 5) :
      multiplicity 5 (5 * a + b).factorial = multiplicity 5 (5 * a).factorial := by
    by_cases h0 : 5 * a + b = 0
    · rw [h0, show 5 * a = 0 by omega]
    -- use the equality (5 - 1) * multiplicity p n! = n - (5.digits n).sum
    -- with n = 5 * a + b and n = 5 * a
    have h1 := @Nat.Prime.sub_one_mul_multiplicity_factorial (5 * a + b) 5 Nat.prime_five
    have h2 := @Nat.Prime.sub_one_mul_multiplicity_factorial (5 * a) 5 Nat.prime_five
    -- it is enough to show that 5.digits (5 * a + b) = b :: 5.digits a
    suffices Nat.digits 5 (5 * a + b) = b :: Nat.digits 5 a by
      have ha : (Nat.digits 5 (5 * a)).sum = (Nat.digits 5 a).sum := by
        by_cases ha0 : a = 0
        · rw [ha0]
        rw [Nat.digits_def' (by norm_num) (by omega), Nat.mul_mod_right, Nat.mul_div_right a (by norm_num)]
        simp only [Nat.reduceLeDiff, List.sum_cons, zero_add]
      simp [this] at h1
      omega
    rw [Nat.digits_def' (by norm_num) (by omega)]
    rw [mul_comm, Nat.mul_add_mod_of_lt hb, mul_comm, Nat.mul_add_div (by norm_num)]
    simp [show b / 5 = 0 by omega]
  -- if a < b then multiplicity 5 (5 * a)! < multiplicity 5 (5 * b)!
  have mult5_fact_lt {a b : ℕ} (hab : a < b) :
      multiplicity 5 (5 * a).factorial < multiplicity 5 (5 * b).factorial := by
    apply FiniteMultiplicity.lt_multiplicity_of_lt_emultiplicity $ hfin5 _
    rw [←FiniteMultiplicity.emultiplicity_eq_multiplicity $ hfin5 _]
    -- the multiplicity of 5 in (5 * n)! is n more than that of n!
    rw [Nat.Prime.emultiplicity_factorial_mul Nat.prime_five, Nat.Prime.emultiplicity_factorial_mul Nat.prime_five]
    rw [FiniteMultiplicity.emultiplicity_eq_multiplicity (hfin5 _)]
    rw [FiniteMultiplicity.emultiplicity_eq_multiplicity (hfin5 _)]
    norm_cast
    apply add_lt_add_of_le_of_lt _ hab
    -- it is left to show that multiplicity 5 a! ≤ multiplcity 5 b!
    -- show that 5 ^ n ∣ a! implies 5 ^ n ∣ b!
    rw [FiniteMultiplicity.multiplicity_le_multiplicity_iff (hfin5 _) (hfin5 _)]
    intro n ⟨d, hd⟩
    -- we have b! = a! * (a + 1).ascFactorial (b - a)
    rw [show b = a + (b - a) by omega, ← Nat.factorial_mul_ascFactorial]
    use d * (a + 1).ascFactorial (b - a)
    rw [hd, mul_assoc]
  -- prove that multiplicity 10 m! = multiplicity 5 m!
  have fact_mult_10 (m : ℕ) : multiplicity 10 m.factorial = multiplicity 5 m.factorial := by
    rw [FiniteMultiplicity.multiplicity_eq_iff $ hfin10 _]
    rw [show 10 = 2 * 5 by norm_num, mul_pow, mul_pow]
    constructor
    -- show that 2 ^ multiplicity 5 m! * 5 ^ multiplicity 5 m! ∣ m!
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · exact Nat.Coprime.pow _ _ rfl
      · apply pow_dvd_of_le_multiplicity
        -- we have multiplicity 5 m! ≤ multiplicity 2 m!
        exact mult_fact_le Nat.prime_two Nat.prime_five (by norm_num)
      · exact pow_multiplicity_dvd 5 m.factorial
    -- show that ¬ 2 ^ (multiplicity 5 m! + 1) * 5 ^ (multiplicity 5 m! + 1) ∣ m!
    · suffices ¬ 5 ^ (multiplicity 5 m.factorial + 1) ∣ m.factorial by
        contrapose! this
        exact dvd_of_mul_left_dvd this
      apply FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt (hfin5 _)
      exact lt_add_one _
  -- multiplicity 5 n! = 0 ↔ n < 5
  have mult5_fact_zero n : multiplicity 5 n.factorial = 0 ↔ n < 5 := by
    rw [multiplicity_eq_zero, Nat.Prime.dvd_factorial Nat.prime_five, not_le]
  -- use classical reasoning to make all predicates decidable
  classical
  -- represent the set from the theorem statement as a difference of two finite sets:
  -- (0, 1991] \ {n | 0 < n ∧ n ≤ 1991 ∧ is_factorial_tail n}
  have : {n | 0 < n ∧ n < 1992 ∧ ¬is_factorial_tail n} = (Finset.Ioc 0 1991 \ Finset.filter is_factorial_tail (Finset.Ioc 0 1991)) := by
    ext n; simp [show n < 1992 ↔ n ≤ 1991 by omega]
    tauto
  rw [this, Set.ncard_coe_Finset, Finset.card_sdiff (Finset.filter_subset _ _)]
  rw [Nat.card_Ioc]
  -- the multiplicity of 5 in 7979! is 1991
  have h_max : multiplicity 5 (7979).factorial = 1991 := by
    have := @Nat.Prime.sub_one_mul_multiplicity_factorial 7979 5 Nat.prime_five
    norm_num at this
    omega
  -- it is enough to show that the cardinality of {n | 0 < n ∧ n ≤ 1991 ∧ is_factorial_tail n}
  -- equals to the cardinality of {n | 0 < n ∧ n ≤ 7979 ∧ 5 ∣ n}
  suffices (Finset.filter is_factorial_tail (Finset.Ioc 0 1991)).card = (Finset.filter (fun n => 5 ∣ n) (Finset.Ioc 0 7979)).card  by
    rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  symm
  -- construct a bijection between two sets to show that they have the same cardinality
  apply Finset.card_bij (fun n _ => multiplicity 5 n.factorial)
  -- show that the function (fun n => multiplicity 5 n!) maps one set into another
  · simp only [Finset.mem_filter, Finset.mem_Ioc, and_imp]
    intro n hn1 hn2 ⟨k, hk⟩
    constructorm* _ ∧ _
    · contrapose! hn1
      rw [nonpos_iff_eq_zero, mult5_fact_zero] at hn1
      omega
    -- demonstrate that multiplicity 5 n! ≤ 1991 when n ≤ 7979
    · rw [hk, ← h_max, show 7979 = 5 * 1595 + 4 by norm_num, mult5_fact_eq $ by norm_num]
      cases' show 5 * k < 5 * 1595 ∨ 5 * k = 5 * 1595 by omega with hk hk
      -- if 5 * k = n < 5 * 1595 = 7975 then multiplicity 5 n! < multiplicity 5 (5 * 1595) = 1991
      · apply le_of_lt
        apply mult5_fact_lt
        omega
      · rw [hk]
    · simp [tail_mult, fact_mult_10]
      use n
  -- show that the function (fun n => multiplicity 5 n!) is injective for 5 ∣ n
  · simp only [Finset.mem_filter, Finset.mem_Ioc, and_imp]
    intro a ha1 ha2 ⟨k, hk⟩ b hb1 hb2 ⟨r, hr⟩ h
    -- we have a = 5 * k and b = 5 * r and we need to show that
    -- multiplicity 5 a! = multiplicity 5 b! implies a = b
    -- without loss of generality, assume that k ≤ r
    wlog hkr : k ≤ r generalizing k r a b
    · symm; exact this b hb1 hb2 r hr a ha1 ha2 k hk (symm h) (by omega)
    cases' lt_or_eq_of_le hkr with hkr hkr
    -- if k < r then multiplicity 5 (5 * k)! = multiplicity 5 (5 * r)! is impossible
    · contrapose! h
      apply ne_of_lt
      rw [hk, hr]
      exact mult5_fact_lt hkr
    omega
  -- show that the function (fun n => multiplicity 5 n!) is surjective
  · simp only [Finset.mem_filter, Finset.mem_Ioc, exists_prop, and_imp]
    simp only [tail_mult, fact_mult_10]
    intro n hn1 hn2 ⟨m, hm0, hm⟩
    have hm5 : 5 ≤ m := by
      contrapose! hm
      rw [(mult5_fact_zero m).mpr hm]
      omega
    -- we have 0 < m, multiplicity 5 m! = n, n ≤ 1991
    -- we need to find x such that 0 < x ≤ 7979 and 5 ∣ x and multiplicity 5 x! = n
    -- take m - m % 5
    use m - m % 5
    constructorm* _ ∧ _ <;> try omega
    · nth_rw 1 [← Nat.div_add_mod m 5, Nat.add_sub_cancel]
      contrapose! hm
      apply ne_of_gt
      apply lt_of_le_of_lt hn2
      rw [←h_max, show 7979 = 5 * 1595 + 4 by norm_num, mult5_fact_eq (by norm_num)]
      rw [← Nat.div_add_mod m 5, mult5_fact_eq (Nat.mod_lt m $ by norm_num)]
      apply mult5_fact_lt
      omega
    · nth_rw 1 [← Nat.div_add_mod m 5] at hm ⊢
      rw [Nat.add_sub_cancel, ← hm, mult5_fact_eq (Nat.mod_lt m $ by norm_num)]
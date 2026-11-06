import Mathlib

open Nat Finset


lemma zmod5eq1 (n : ℕ) (h : (-2) ^ n ≡ 1 [ZMOD 5]): 4 ∣ n := by 
  obtain mod_or : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  obtain h0 | h1 | h2 | h3 := mod_or
  · exact dvd_of_mod_eq_zero h0
  · by_contra hc0
    have nmod : n % 4 = 1 % 4 := by 
      simp [h1]
    obtain aux := Nat.ModEq.dvd (Eq.symm nmod)
    obtain ⟨k, hk⟩ := aux
    have neq : (n : ℤ) = (4 : ℕ) * k + 1:= by
      rw [←hk]
      simp
    have kge : k ≥ 0 := by
      by_contra hc
      simp at hc
      have kle : k ≤ -1 := by linarith
      have ineq : (4 : ℕ) * k + 1 ≤ -1 := by 
        omega
      rw [←neq] at ineq
      nlinarith
    have existt : ∃ (t : ℕ), k = t := by 
      use k.toNat
      simp [kge]
    obtain ⟨t, ht⟩ := existt
    rw [ht] at neq
    norm_cast at neq
    rw [neq] at h
    rw [pow_add, pow_mul] at h
    have mod1 : ((-2) ^ 4) ≡ 1 [ZMOD 5] := by 
      rfl
    have mod2 : 3 ≡ 1 [ZMOD 5] := by 
      calc 
        _ ≡ 1 * (-2) [ZMOD 5] := by 
          rfl
        _ ≡ ((-2) ^ 4) ^ t * (-2) ^ 1 [ZMOD 5] := by 
          refine Int.ModEq.symm (Int.ModEq.mul ?_ rfl)
          rw [show (1 : ℤ) = 1 ^ t by norm_num]
          exact Int.ModEq.pow t mod1
        _ ≡ 1 [ZMOD 5] := by
          exact h
    obtain dvd1 := Int.ModEq.dvd mod2
    norm_num at dvd1
  · by_contra hc0
    have nmod : n % 4 = 2 % 4 := by 
      simp [h2]
    obtain aux := Nat.ModEq.dvd (Eq.symm nmod)
    obtain ⟨k, hk⟩ := aux
    have neq : (n : ℤ) = (4 : ℕ) * k + 2:= by
      rw [←hk]
      simp
    have kge : k ≥ 0 := by
      by_contra hc
      simp at hc
      have kle : k ≤ -1 := by linarith
      have ineq : (4 : ℕ) * k + 2 ≤ -1 := by 
        omega
      rw [←neq] at ineq
      nlinarith
    have existt : ∃ (t : ℕ), k = t := by 
      use k.toNat
      simp [kge]
    obtain ⟨t, ht⟩ := existt
    rw [ht] at neq
    norm_cast at neq
    rw [neq] at h
    rw [pow_add, pow_mul] at h
    have mod1 : ((-2) ^ 4) ≡ 1 [ZMOD 5] := by 
      rfl
    have mod2 : 4 ≡ 1 [ZMOD 5] := by 
      calc 
        _ ≡ 1 * (-2) ^ 2 [ZMOD 5] := by 
          rfl
        _ ≡ ((-2) ^ 4) ^ t * (-2) ^ 2 [ZMOD 5] := by 
          refine Int.ModEq.symm (Int.ModEq.mul ?_ rfl)
          rw [show (1 : ℤ) = 1 ^ t by norm_num]
          exact Int.ModEq.pow t mod1
        _ ≡ 1 [ZMOD 5] := by
          exact h
    obtain dvd1 := Int.ModEq.dvd mod2
    norm_num at dvd1
  · by_contra hc0
    have nmod : n % 4 = 3 % 4 := by 
      simp [h3]
    obtain aux := Nat.ModEq.dvd (Eq.symm nmod)
    obtain ⟨k, hk⟩ := aux
    have neq : (n : ℤ) = (4 : ℕ) * k + 3:= by
      rw [←hk]
      simp
    have kge : k ≥ 0 := by
      by_contra hc
      simp at hc
      have kle : k ≤ -1 := by linarith
      have ineq : (4 : ℕ) * k + 3 ≤ -1 := by 
        omega
      rw [←neq] at ineq
      nlinarith
    have existt : ∃ (t : ℕ), k = t := by 
      use k.toNat
      simp [kge]
    obtain ⟨t, ht⟩ := existt
    rw [ht] at neq
    norm_cast at neq
    rw [neq] at h
    rw [pow_add, pow_mul] at h
    have mod1 : ((-2) ^ 4) ≡ 1 [ZMOD 5] := by 
      rfl
    have mod2 : 2 ≡ 1 [ZMOD 5] := by 
      calc 
        _ ≡ 1 * (-2) ^ 3 [ZMOD 5] := by 
          rfl
        _ ≡ ((-2) ^ 4) ^ t * (-2) ^ 3 [ZMOD 5] := by 
          refine Int.ModEq.symm (Int.ModEq.mul ?_ rfl)
          rw [show (1 : ℤ) = 1 ^ t by norm_num]
          exact Int.ModEq.pow t mod1
        _ ≡ 1 [ZMOD 5] := by
          exact h
    obtain dvd1 := Int.ModEq.dvd mod2
    norm_num at dvd1


/- 3. (CUB 3) ${ }^{\mathrm{IMO} 1}$ Let $n>m \geq 1$ be natural numbers such that the groups of the last three digits in the decimal representation of $1978^{m}, 1978^{n}$ coincide. Find the ordered pair $(m, n)$ of such $m, n$ for which $m+n$ is minimal. -/
theorem number_theory_23682 :
    IsLeast {p : ℕ × ℕ | p.1 > p.2 ∧ p.2 ≥ 1 ∧ (1978^p.2) % 1000 = (1978^p.1) % 1000} (103, 3) := by 
  unfold IsLeast
  constructor
  -- first prove that (103, 3) ∈ {p | p.1 > p.2 ∧ p.2 ≥ 1 ∧ 1978 ^ p.2 % 1000 = 1978 ^ p.1 % 1000}
  · simp
  · -- then prove that it is the minimal
    unfold lowerBounds
    simp
    intro n m hmn hm h 
    have dvd1 : 1000 ∣ 1978 ^ n - 1978 ^ m := by
      have modeq : (1978 ^ n - 1978 ^ m) % 1000 = 0 := by omega
      exact Nat.dvd_of_mod_eq_zero modeq
    have eq1 : 1978 ^ n - 1978 ^ m = 1978 ^ m * (1978 ^ (n-m)-1) := by
      have aux1 : n = m + (n-m) := by omega
      conv => 
        lhs 
        rw [aux1]
      rw [pow_add]
      have pos : 1978 ^ (n - m) >  0 := by 
        positivity
      have aux2 : 1978 ^ m * (1978 ^ (n - m) - 1) = 
        1978 ^ m * 1978 ^ (n - m) - 1978 ^ m * 1 := by
        exact Nat.mul_sub_left_distrib (1978 ^ m) (1978 ^ (n - m)) 1
      rw [aux2]
      simp
    rw [eq1] at dvd1
    have eq2 : 1000 = 8 * 125 := by norm_num
    have coprime1 : Nat.Coprime 8 (1978 ^ (n - m) - 1) := by 
      have odd1 : Odd (1978 ^ (n - m) - 1) := by 
        have even1 : Even (1978 ^ (n - m)) := by
          refine (Nat.even_pow' ?_).mpr ?_
          omega
          use 989
        refine Nat.Even.sub_odd ?_ even1 ?_
        have pos : 1978 ^ (n - m) >  0 := by 
          positivity
        linarith
        use 0
        norm_num
      -- Nat.coprime_two_left
      have aux : 8 = 2 ^ 3 := by norm_num
      rw [aux]
      refine (coprime_pow_left_iff ?_ _ _).mpr ?_
      linarith
      simp [odd1]
    have dvd2 : 8 ∣ 1978 ^ m := by
      have dvd3 : 8 ∣ 1978 ^ m * (1978 ^ (n - m) - 1) := by 
        have aux : 8 ∣ 1000 := by 
          norm_num
        exact dvd_trans aux dvd1
      exact Coprime.dvd_of_dvd_mul_right coprime1 dvd3
    -- pow_dvd_of_le_multiplicity
    have eq8 : 8 = 2 ^ 3 := by norm_num
    rw [eq8] at dvd2
    -- FiniteMultiplicity.le_multiplicity_of_pow_dvd
    have h2 : FiniteMultiplicity 2 (1978 ^ m) := by 
      refine Nat.finiteMultiplicity_iff.mpr ?_
      constructor
      linarith
      positivity
    obtain h1 := FiniteMultiplicity.le_multiplicity_of_pow_dvd
      h2 dvd2
    have mul1 : multiplicity 2 (1978 ^ m) = m := by 
      -- FiniteMultiplicity.multiplicity_pow
      have h3 : multiplicity 2 (1978 ^ m) = m * multiplicity 2 1978 := by
        apply FiniteMultiplicity.multiplicity_pow
        refine prime_iff.mp ?_
        norm_num
        refine Nat.finiteMultiplicity_iff.mpr ?_
        constructor
        linarith
        positivity
      rw [h3]
      have h4 : multiplicity 2 1978 = 1 := by 
        refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
        norm_num
        norm_num
      simp [h4]
    rw [mul1] at h1
    constructor
    have h3 : Coprime (5 ^ 3) (1978 ^ m) := by 
      exact Coprime.pow 3 m rfl
    have dvd3 : 5 ^ 3 ∣ (1978 ^ m) * (1978 ^ (n - m) - 1):= by
      have aux : 5 ^ 3 ∣ 1000 := by
        norm_num
      exact dvd_trans aux dvd1
    have dvd4 : 5 ^ 3 ∣ (1978 ^ (n - m) - 1) := by 
      exact Coprime.dvd_of_dvd_mul_left h3 dvd3
    have modeq : 1978 ^ (n - m) ≡ 1 [ZMOD 125] := by 
      norm_num at dvd4
      zify at dvd4
      have cast1 : ↑(1978 ^ (n - m) - 1 : ℕ) = ((1978 : ℤ) ^ (n - m) -1 ) := by
        have ge1 : 1978 ^ (n - m) ≥ 1 := by 
          exact one_le_pow' (n - m) 1977
        have ge2 : (1978 : ℤ) ^ (n - m) - 1 ≥ 0 := by 
          zify at ge1
          linarith
        norm_cast
      rw [cast1] at dvd4
      exact Int.ModEq.symm ((fun {n a b} => Int.modEq_iff_dvd.mpr) dvd4)
    have aux2 : 1978 ≡ -2 [ZMOD 5] := by
      exact rfl
    have mod1 : 1978 ^ (n - m) ≡ (-2) ^ (n - m) [ZMOD 5] := by
      exact Int.ModEq.pow (n - m) aux2
    have modeq2 : (-2) ^ (n - m) ≡ 1 [ZMOD 5] := by
      apply Int.ModEq.trans (Int.ModEq.symm mod1) 
      refine Int.ModEq.of_mul_left 25 ?_
      norm_num
      exact modeq
    -- by analysis the ZMODEq in modeq2, we have 4 ∣ n - m
    have dvdn4 : 4 ∣ n - m := by exact zmod5eq1 (n - m) modeq2
    obtain ⟨k, hk⟩ := dvdn4
    rw [hk] at modeq
    have modeq3 : 1978 ^ 4 ≡ 6 [ZMOD 125] := by 
      exact rfl
    have eq3 : (1978 : ℤ) ^ (4 * k) = (1978 ^ 4) ^ k := by
      rw [pow_mul]
    rw [eq3] at modeq
    have modeq4 : 6 ^ k ≡ 1 [ZMOD 125] := by 
      calc 
        _ ≡ (1978 ^ 4) ^ k  [ZMOD 125] := by
          exact Int.ModEq.pow k modeq3
        _ ≡ 1 [ZMOD 125]:= by 
          exact modeq
    -- 6 ^ k ≡ 1 + 5 * k + 25 * choose k 2 [ZMOD 125]
    have knezero : k ≠ 0 := by 
        by_contra hc
        rw [hc] at hk
        simp at hk
        have neqm : n = m := by 
          omega
        linarith
    have kge : k ≥ 3 := by 
        have kgt : k > 0 := by 
          positivity
        by_contra hc
        simp at hc
        interval_cases k
        norm_num at modeq4
        obtain dvdhc := Int.ModEq.dvd modeq4
        norm_num at dvdhc
        obtain dvdhc := Int.ModEq.dvd modeq4
        norm_num at dvdhc
    have modeq5 : 6 ^ k ≡  1 + 5 * k + 25 * Nat.choose k 2 [ZMOD 125] := by 
      have eq_6 : (6 : ℤ) = 1 + 5 := by 
        norm_num
      rw [eq_6, add_comm, add_pow]
      -- add_pow
      -- the index 5 ^ (k - m) ≡ 0 [ZMOD 125] when k - m ≥ 3
      -- then we only leave the first three terms
      have disj_aux : Disjoint (Icc 0 2) (Ico 3 (k + 1)) := by 
        refine disjoint_left.mpr ?_
        intro a ha
        simp at ha ⊢
        intro h
        omega
      have seteq : range (k + 1) = (Icc 0 2).disjUnion (Ico 3 (k + 1)) disj_aux := by
        refine Finset.ext_iff.mpr ?_
        intro x 
        constructor
        · intro hx
          simp at hx ⊢
          by_cases hxle2 : x ≤ 2 
          · left 
            linarith
          · right
            simp at hxle2
            constructor
            linarith
            linarith
        · intro hx
          simp at hx ⊢ 
          obtain hx | hx := hx
          linarith
          linarith
      rw [seteq, sum_disjUnion]
      have aux3 : ∑ x ∈ Ico 3 (k + 1), 5 ^ x * 1 ^ (k - x) * ↑(k.choose x) ≡ 0 [ZMOD 125] := by 
        apply Int.ModEq.symm
        apply Int.modEq_of_dvd
        simp
        apply dvd_sum
        intro i hi
        simp at hi
        obtain ⟨hi1, hi2⟩ := hi
        have dvd1 : (125) ∣ 5 ^ i := by 
          rw [show 125 = 5 ^3 by norm_num]
          exact pow_dvd_pow_iff_le_right'.mpr hi1
        zify at dvd1
        exact Dvd.dvd.mul_right dvd1 ↑(k.choose i)
      have aux4 : ∑ x ∈ Icc 0 2, (5 : ℤ) ^ x * 1 ^ (k - x) * ↑(k.choose x) = 1 + 5 * (k : ℤ) + 25 * ↑(k.choose 2) := by 
        simp
        calc 
          _ = ((5 : ℤ) ^ 0 * ↑(k.choose 0)) + 5 ^ 1 * ↑(k.choose 1) + 5 ^ 2 * ↑(k.choose 2) := by 
            have aux : Icc 0 2 = {0 , 1 , 2} := by 
              rfl
            rw [aux]
            simp
            ring
          _ = _ := by
            simp
      rw [aux4]
      apply Int.ModEq.symm
      apply Int.modEq_of_dvd
      simp
      simp at aux3
      exact Int.dvd_of_emod_eq_zero aux3
      -- by the above ZMOD equality, we conclude that
    have dvd5 : 125 ∣ 5 * k * (5 * k -3 ) := by 
      -- 5 * k + 25 * Nat.choose k 2 ≡ 5 * k * (5 * k -3 ) [ZMOD 125]
      have mod2 : 1 ≡  1 + 5 * ↑k + 25 * ↑(k.choose 2) [ZMOD 125] := by 
        exact Int.ModEq.trans (id (Int.ModEq.symm modeq4)) modeq5
      obtain mod3 := Int.ModEq.dvd mod2
      ring_nf at mod2
      rw [Nat.choose_two_right] at mod3
      have cast1 : (k - 1 : ℕ) = (k : ℤ) - 1 := by 
        have ge : (k : ℤ) - 1 ≥ 0 := by
          zify at kge
          linarith
        omega
      have mod4 : ((k : ℤ) * 5 + ↑(k * (k - 1) / 2) * 25) * 2 
        = 5 * k * (5 * k - 3) := by 
        calc 
          _ = 10 * (k : ℤ) + 25 * ((k * (k - 1) / 2) * 2 : ℕ) := by 
            norm_num
            ring
          _ = _ := by 
            have aux : (k * (k - 1) / 2) * 2 = k * (k - 1) := by 
              refine Nat.div_mul_cancel ?_
              by_cases hkeven : Even k
              · have dvd2 : 2 ∣ k := by 
                  exact even_iff_two_dvd.mp hkeven
                exact Dvd.dvd.mul_right dvd2 (k - 1)
              · have heven' : Even (k - 1) := by 
                  simp at hkeven
                  refine Nat.Odd.sub_odd hkeven ?_
                  use 0
                  simp
                have dvd2 : 2 ∣ k - 1 := by
                  exact even_iff_two_dvd.mp heven'
                exact Dvd.dvd.mul_left dvd2 k
            rw [aux]
            
            norm_num
            rw [cast1] 
            ring
      zify at mod3
      zify
      have cast2 : (5 * k - 3 : ℕ) = (5 : ℤ) * k -3 := by 
        have ge1 : 5 * k - (3 : ℤ) ≥ 0:= by
          linarith
        omega
      rw [cast2, ←mod4]
      have aux3 : ((k : ℤ) * 5 + ↑(k * (k - 1) / 2 : ℕ) * 25) = 
        1 + 5 * ↑k + 25 * (↑k * ↑(k - 1 : ℕ) / 2) - 1 := by 
        norm_num
        ring
      rw [aux3]
      exact Dvd.dvd.mul_right mod3 2

    have coprime3 : Nat.Coprime 125 (5 * k - 3) := by 
      have aux : 125 = 5 ^ 3 := by
        norm_num 
      rw [aux]
      apply Coprime.pow_left 3
      have ge_aux : 5 * k ≥ 3 := by 
        linarith
      have co_aux : Nat.Coprime 5 3 := by 
        norm_num
      have dvd_aux : 5 ∣ 5 * k := by
        simp
      by_contra hc'
      have prime5 : Nat.Prime 5 := by 
        norm_num
      have dvd6 : 5 ∣ 5 * k - 3 := by
        exact (Prime.dvd_iff_not_coprime prime5).mpr hc'
      have eq_3 : 3 = 5 * k - (5 * k - 3) := by 
        omega
      have dvd7 : 5 ∣ 3 := by
        rw [eq_3]
        refine Nat.dvd_sub ?_ dvd_aux dvd6
        omega
      norm_num at dvd7
    have dvd8 : 125 ∣ 5 * k := by
      exact Coprime.dvd_of_dvd_mul_right coprime3 dvd5
    have dvd9 : 25 ∣ k := by 
      omega
    have kge2 : k ≥ 25 := by 
      apply le_of_dvd 
      positivity
      exact dvd9
    have kge3 : n - m ≥ 100 := by omega
    have neq : n = (n - m) + m := by 
      omega
    linarith
    -- the goal m ≥ 3
    exact h1

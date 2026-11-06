import Mathlib

/- (a^n - 1) / (a-1) is odd, if a,n both odd.  -/
lemma l_odd_odd_pow_sub_one_div_sub_one {a n: ℕ}
  (ha: Odd a) (age: a ≥ 2) (hn: Odd n): Odd ((a^n - 1) / (a - 1)) := by
  rw [← Nat.geomSum_eq age]
  rw [Finset.odd_sum_iff_odd_card_odd]
  have: ({x ∈ Finset.range n | Odd (a ^ x)}) = Finset.range n := by
    ext _
    simp only [Finset.mem_filter, Finset.mem_range,
    and_iff_left_iff_imp]
    intro _
    apply Odd.pow ha
  simp [this, hn]

/- if a is odd, then a^2+1 exactly divisible by 2.  -/
lemma l_odd_sq_add_one_eq_two_mul_odd {a: ℕ} (ha: Odd a):
  ∃ b, a^2+1 = 2*b ∧ Odd b := by
  have h1: Even (a^2+1) := by
    apply Odd.add_one ?_
    apply ha.pow
  rw [even_iff_exists_two_mul] at h1
  rcases h1 with ⟨b, hb⟩
  have h2: a^2 + 1 = (a^2 - 1) + 2 := by
    have: 0 < a := Odd.pos ha
    replace: 1 ≤ a^2 := Nat.one_le_pow 2 a this
    zify
    rw [Nat.cast_sub this]
    push_cast
    ring
  have h3: 2 * 2 ∣ (a^2 - 1) := by
    rw [← one_pow 2, Nat.sq_sub_sq]
    apply Nat.mul_dvd_mul ?_ ?_
    <;> rw [← even_iff_two_dvd]
    · exact Odd.add_one ha
    · refine Nat.Odd.sub_odd ha ?_
      exact Nat.odd_iff.mpr rfl
  refine ⟨b, hb, ?_⟩
  by_contra!
  replace: 2 * 2 ∣ 2 := by
    suffices 2*2 ∣ a^2-1 + 2 by
      exact (Nat.dvd_add_iff_right h3).mpr this
    rw [← h2, hb]
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at this
    exact Nat.mul_dvd_mul_left 2 this
  norm_num at this

/- since a^2+1 only contain one factor 2, a^2+1, a^4 + 1, ..., 2-mutiplicity of product is 1+1+...+1. -/
lemma l_odd_sq_add_one_prod_eq_two_pow_mul_odd {a:ℕ} (k:ℕ) (ha: Odd a):
  ∃ b, ∏ i ∈ Finset.range k, (a^(2^(i+1)) + 1) = 2^k * b ∧ Odd b := by
  induction' k with k ih
  · simp
  · rcases ih with ⟨b, hb, oddb⟩
    obtain ⟨b', hb', oddb'⟩: ∃ b', a^(2^(k+1))+1 = 2*b' ∧ Odd b' := by
      rw [pow_add, pow_one, pow_mul]
      apply l_odd_sq_add_one_eq_two_mul_odd
      apply ha.pow
    use (b*b')
    refine ⟨?_, oddb.mul oddb'⟩
    rw [Finset.prod_range_succ, hb', hb]
    ring

/- 27. (ROM 1) Let $m$ be a positive odd integer, $m \geq 2$.
Find the smallest positive integer $n$ such that $2^{1989}$ divides $m^{n}-1$. -/
theorem number_theory_24236 {m s: ℕ} (hm: Odd m) (mge: m ≥ 2)
  (hs: IsGreatest {s':ℕ | 2^s' ∣ m+1 ∨ 2^s' ∣ m-1} s):
  IsLeast {n:ℕ | 0 < n ∧ 2^1989 ∣ m^n - 1}
    ( if (2^1989 ∣ m - 1) then 1 else 2^((1989-s) - 1 + 1) ) := by

  -- factorization m^2^k - 1.
  -- we claim m^2^k - 1 = (m^2-1)(m^2+1)(m^4+1)...(m^2^(k-1) + 1)
  have h1 {k: ℕ} (hk: k ≥ 1): m^(2^k) - 1 =
    (m^2-1) * ∏ i ∈ Finset.range (k-1), (m^(2^(i+1))+1) := by
    induction' k,hk using Nat.le_induction with k hk ih
    · simp
    · nth_rw 1 [pow_succ, pow_mul, ← one_pow 2, Nat.sq_sub_sq,
      mul_comm]
      have: k+1-1 = (k-1) + 1 := by simp [hk]
      rw [this, Finset.prod_range_succ, Nat.sub_add_cancel hk]
      simp [← mul_assoc, ih]

  -- by definition of s, m^2-1 is "exactly divisible" by 2^(s+1)
  rw [IsGreatest, upperBounds] at hs
  simp only [Set.mem_setOf_eq] at hs

  have h2: 2^(s+1) ∣ m^2 - 1 := by
    nth_rw 2 [← one_pow 2]
    rw [Nat.sq_sub_sq, pow_succ]
    have := hs.left
    rcases this with hh | hh
    · refine Nat.mul_dvd_mul hh ?_
      rw [← even_iff_two_dvd]
      refine Nat.Odd.sub_odd hm ?_
      exact Nat.odd_iff.mpr rfl
    · rw [mul_comm _ 2]
      refine Nat.mul_dvd_mul ?_ hh
      rw [← even_iff_two_dvd]
      exact Odd.add_one hm
  rcases h2 with ⟨a, ha⟩
  -- to express the "exactly divide" relation, we argue after taking out 2^(s+1),
  -- the remaining part a is odd.
  have h2: Odd a := by
    have := hs.left
    nth_rw 1 [← one_pow 2] at ha
    rw [Nat.sq_sub_sq] at ha
    -- s ≠ 0, and if s = 1, trivial.
    have snz: s ≠ 0 := by
      replace: 2^1 ∣ m+1 := by
        rw [pow_one, ← even_iff_two_dvd]
        apply hm.add_one
      replace := hs.right (Or.inl this)
      exact Nat.not_eq_zero_of_lt this
    by_contra! hha
    rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hha
    replace hha: 2^s * (2*2) ∣ (m+1) * (m-1) := by
      rw [← mul_assoc, ← pow_succ, ha]
      apply Nat.mul_dvd_mul_left _ hha
    rcases this with hh | hh
    · have hh' := hh
      obtain ⟨c, hc⟩ := hh
      have hhc: Odd c := by
        by_contra!
        replace: 2^(s+1) ∣ m+1 := by
          rw [pow_succ, hc]
          rw [Nat.not_odd_iff_even, even_iff_two_dvd] at this
          apply Nat.mul_dvd_mul_left _ this
        replace := hs.right (Or.inl this)
        simp at this
      replace hha: 2*2 ∣ (m-1) := by
        rw [hc, mul_assoc] at hha
        suffices (2*2) ∣ c*(m-1) by
          apply (Nat.Coprime.dvd_mul_left ?_).mp this
          rw [← pow_two]
          refine Nat.Coprime.pow_left 2 ?_
          exact Nat.coprime_two_left.mpr hhc
        apply Nat.dvd_of_mul_dvd_mul_left (by simp) hha
      have: 2*2 ∣ 2 := by
        have: m+1 = (m-1) + 2 := by omega
        rw [this] at hh'
        replace hh': 2*2 ∣ m-1 + 2 := by
          apply Dvd.dvd.trans ?_ hh'
          rw [← pow_two]
          refine Nat.pow_dvd_pow 2 ?_
          apply hs.right
          simp only [pow_two, hha, or_true]
        exact (Nat.dvd_add_iff_right hha).mpr hh'
      norm_num at this
    · have hh' := hh
      obtain ⟨c, hc⟩ := hh
      have hhc: Odd c := by
        by_contra!
        replace: 2^(s+1) ∣ m-1 := by
          rw [pow_succ, hc]
          rw [Nat.not_odd_iff_even, even_iff_two_dvd] at this
          apply Nat.mul_dvd_mul_left _ this
        replace := hs.right (Or.inr this)
        simp at this
      replace hha: 2*2 ∣ (m+1) := by
        rw [hc] at hha
        suffices (2*2) ∣ c*(m+1) by
          apply (Nat.Coprime.dvd_mul_left ?_).mp this
          rw [← pow_two]
          refine Nat.Coprime.pow_left 2 ?_
          exact Nat.coprime_two_left.mpr hhc
        rw [← mul_assoc (m+1), mul_comm _ c, ← mul_assoc c,
        mul_comm (c*(m+1))] at hha
        apply Nat.dvd_of_mul_dvd_mul_left (by simp) hha
      have: 2*2 ∣ 2 := by
        have: m+1 = (m-1) + 2 := by omega
        rw [this] at hha
        replace hh': 2*2 ∣ m-1 := by
          apply Dvd.dvd.trans ?_ hh'
          rw [← pow_two]
          refine Nat.pow_dvd_pow 2 ?_
          apply hs.right
          simp only [pow_two, this, hha, true_or]
        exact (Nat.dvd_add_iff_right hh').mpr hha
      norm_num at this



  rw [IsLeast, lowerBounds]
  simp only [Set.mem_setOf_eq, Nat.ofNat_pos, pow_pos, true_and, and_imp]
  constructor

  · -- verify 2^(1989-s) satisfy the condition when s < 1989.
    -- and when s ≥ 1989, the answer is 2 or 1, depends on whether 2^1989 divide m-1.
    by_cases h: 2^1989 ∣ m - 1
    · rw [if_pos h, pow_one]
      exact ⟨(by norm_num), h⟩
    rw [if_neg h]
    by_cases sge: s ≥ 1989
    · have: 1989 - s - 1 = 0 := by
        rw [Nat.sub_eq_zero_of_le]
        rw [Nat.sub_eq_zero_of_le sge]
        simp
      simp only [this, zero_add, pow_one, Nat.ofNat_pos, true_and]
      rw [← one_pow 2, Nat.sq_sub_sq]
      have := hs.left
      have hdvd: 2^1989 ∣ 2^s := by
        apply Nat.pow_dvd_pow 2
        exact sge
      rcases this with hh | hh
      all_goals apply hdvd.trans ?_
      · exact Dvd.dvd.mul_right hh (m - 1)
      · exact hh.mul_left _
    push_neg at sge
    replace sge: 0 < 1989 - s := by
      exact Nat.sub_pos_of_lt sge
    change 1 ≤ 1989 - s at sge
    rw [Nat.sub_add_cancel sge]
    refine ⟨(by simp), ?_⟩
    -- m^2^n - 1 = (m^2-1) (m^2+1)(m^4+1)...(m^2^(n-1)+1)
    -- when n = 1989 - s, m^2-1 contain 2^s, and the remain part contribute 2^n = 2^(1989-s).
    -- the power index add to 1989, done.
    rw [h1 sge, ha, mul_comm _ a, mul_assoc]
    have := l_odd_sq_add_one_prod_eq_two_pow_mul_odd (1989-s-1) hm
    rcases this with ⟨b, hb, oddb⟩
    rw [hb]
    have: a*(2^(s+1)*(2^(1989-s-1)*b)) = (a*b) * (2^(s+1)*2^(1989-s-1)) := by
      ring
    rw [this]
    apply Dvd.dvd.mul_left
    rw [← Nat.pow_add]
    have: s+1 + (1989-s-1) = 1989 := by
      rw [Nat.sub_sub]
      replace: 1+s ≤ 1989 := by
        apply Nat.add_le_of_le_sub ?_ sge
        exact (Nat.lt_of_sub_pos sge).le
      rw [add_comm] at this
      rw [Nat.add_sub_cancel' this]
    rw [Nat.sub_sub, Nat.add_sub_cancel']
    apply Nat.add_le_of_le_sub' ?_ sge
    exact (Nat.lt_of_sub_pos sge).le

  · intro n npos hdvd
    rcases (Nat.exists_eq_two_pow_mul_odd npos.ne') with ⟨k, n, hn, rfl⟩
    have nge: n ≥ 1 := by
      refine Nat.one_le_iff_ne_zero.mpr ?_
      exact Nat.ne_of_odd_add hn
    -- single out s ≥ 1989 and 2^1989 divide m - 1 case.
    by_cases h': 2^1989 ∣ m - 1
    · rw [if_pos h']
      refine one_le_mul ?_ nge
      exact Nat.one_le_two_pow
    rw [if_neg h']
    by_cases sge: s ≥ 1989
    · simp only [sge, Nat.sub_eq_zero_of_le, zero_tsub,
      zero_add, pow_one, ge_iff_le]
      suffices k ≠ 0 by
        refine le_mul_of_le_of_one_le ?_ nge
        exact Nat.le_self_pow this 2
      rintro keq
      simp only [keq, pow_zero, one_mul] at hdvd
      have: m^n - 1 = (m-1) * ( (m^n-1) / (m-1) ) := by
        symm
        apply Nat.mul_div_cancel_left' ?_
        nth_rw 2 [← one_pow n]
        apply nat_sub_dvd_pow_sub_pow
      absurd h'
      rw [this] at hdvd
      apply (Nat.Coprime.dvd_mul_right ?_).mp hdvd
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      apply l_odd_odd_pow_sub_one_div_sub_one hm mge hn
    push_neg at sge
    replace sge: 1 ≤ 1989 - s := by
      exact Nat.sub_pos_of_lt sge
    -- suffices to consider n is 2-power case.
    suffices 2^(1989-s) ≤ 2^k by
      rw [Nat.sub_add_cancel sge]
      apply this.trans ?_
      apply Nat.le_mul_of_pos_right _ nge
    replace hdvd: 2^1989 ∣ m^(2^k) - 1 := by
      have hh1: m^(2^k*n) - 1 = (m^(2^k) - 1) *
        ( ((m^(2^k))^n - 1) / (m^(2^k) - 1)  ) := by
        symm
        rw [pow_mul]
        apply Nat.mul_div_cancel_left' ?_
        nth_rw 2 [← one_pow n]
        apply nat_sub_dvd_pow_sub_pow
      have hh2: Odd  ( ((m^(2^k))^n - 1) / (m^(2^k) - 1)  ) := by
        have: 2 ≤ m^(2^k) := by
          apply mge.trans ?_
          apply Nat.le_self_pow (by simp)
        apply l_odd_odd_pow_sub_one_div_sub_one ?_ this hn
        apply hm.pow
      rw [hh1] at hdvd
      apply (Nat.Coprime.dvd_mul_right ?_).mp hdvd
      rw [← Nat.coprime_two_left] at hh2
      apply hh2.pow_left
    -- now we can focus on n is 2^k case.
    -- if k = 0, s ≥ 1989
    by_cases hk: k = 0
    · simp only [hk, pow_zero, pow_one] at hdvd
      have := hs.right
      specialize @this 1989 (Or.inr hdvd)
      simp only [this, Nat.sub_eq_zero_of_le, pow_zero, hk, le_refl]
    replace hk: k ≥ 1 := by omega
    -- else, write m^2^k-1 = (m^2-1)(m^2+1)(m^4+1) ... (m^2^(k-1)+1)
    rw [h1 hk, ha] at hdvd
    -- the divide relation says 2^1989 divide 2^(s+1) mul 2^(k-1), so 1989 ≤ s+k, done.
    have := l_odd_sq_add_one_prod_eq_two_pow_mul_odd (k-1) hm
    rcases this with ⟨b, hb, oddb⟩
    rw [hb] at hdvd
    replace hdvd: 2^1989 ∣ (a*b) * (2^(s+1) * 2^(k-1)) := by
      have: 2^(s+1)*a*(2^(k-1)*b) = (a*b) * (2^(s+1) * 2^(k-1)) := by ring
      rwa [this] at hdvd
    have: Nat.Coprime (2^1989) (a*b) := by
      apply Nat.Coprime.pow_left
      rw [Nat.coprime_two_left]
      apply h2.mul oddb
    rw [this.dvd_mul_left, ← pow_add, show s+1+(k-1) = s+k by omega] at hdvd
    replace hdvd: 1989 ≤ s+k := by
      generalize 1989 = c at hdvd ⊢
      exact Nat.pow_dvd_pow_iff_le_right'.mp hdvd
    apply Nat.le_of_dvd (by simp) ?_
    rw [Nat.pow_dvd_pow_iff_le_right']
    exact Nat.sub_le_iff_le_add'.mpr hdvd
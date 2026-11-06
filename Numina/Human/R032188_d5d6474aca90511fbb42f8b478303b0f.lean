import Mathlib


/- 20. N2 (RUS) ${ }^{\mathrm{IMO} 4}$ The positive integers $a$ and $b$ are such that the numbers $15 a+16 b$ and $16 a-15 b$ are both squares of positive integers. What is the least possible value that can be taken on by the smaller of these two squares? -/
theorem number_theory_24693:
  IsLeast {u:ℕ | ∃ (x y:ℕ), u = min x y ∧ 0 < x ∧ 0 < y ∧
    ∃ (a b: ℕ), (15*a+16*b = x^2) ∧ (16*a-15*b = y^2)} 481 := by

  -- before start, we prove following lemma.

  -- if p ∣ x^m-y^m, p ∣ x^n - y^n, then p ∣ x^d-y^d, where d is gcd (m,n).
  have aux1 {x y m n p: ℕ} (h1: x^m ≡ y^m [ZMOD p]) (h2: x^n ≡ y^n [ZMOD p])
    (hx: x.Coprime p) (hy: y.Coprime p) (pp: Nat.Prime p):
    x^(m.gcd n) ≡ y^(m.gcd n) [ZMOD p] := by
    -- let a be inverse of x.
    rcases (Int.mod_coprime hx) with ⟨a,ha⟩
    -- then (ya)^d ≡ 1 mod p.
    have h3: y^(m.gcd n) * a^(m.gcd n) ≡ 1 [ZMOD p] := by
      rw [← mul_pow]
      have ham: x^m * a^m ≡ 1 [ZMOD p] := by
        rw [← mul_pow, ← one_pow m]
        apply Int.ModEq.pow _ ha
      have han: x^n * a^n ≡ 1 [ZMOD p] := by
        rw [← mul_pow, ← one_pow n]
        apply Int.ModEq.pow _ ha
      have h3: (y*a)^m ≡ 1 [ZMOD p] := by
        rw [mul_pow]
        apply Int.ModEq.trans ?_ ham
        apply Int.ModEq.mul h1.symm rfl
      have h4: (y*a)^n ≡ 1 [ZMOD p] := by
        rw [mul_pow]
        apply Int.ModEq.trans ?_ han
        apply Int.ModEq.mul h2.symm rfl
      rw [← ZMod.intCast_eq_intCast_iff] at h3 h4 ⊢
      push_cast at h3 h4 ⊢
      apply pow_gcd_eq_one _ h3 h4
    -- and clearly x^d a^d = 1
    have h4: x^(m.gcd n) * a^(m.gcd n) ≡ 1 [ZMOD p] := by
      rw [← mul_pow, ← one_pow (m.gcd n)]
      exact Int.ModEq.pow (m.gcd n) ha
    replace h4 := h4.trans h3.symm
    -- cancel a^d from both sides, done.
    have h5: IsCoprime (p:ℤ) (a^(m.gcd n)) := by
      refine IsCoprime.pow_right ?_
      rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp pp)]
      by_contra!
      have not_ha: x*a ≡ 0 [ZMOD p] := by
        refine Dvd.dvd.modEq_zero_int ?_
        apply Dvd.dvd.mul_left this
      replace := ha.symm.trans not_ha
      have hh1: (1:ℤ) = ↑(1:ℕ) := by simp
      have hh2: (0:ℤ) = ↑(0:ℕ) := by simp
      rw [hh1, hh2, Int.natCast_modEq_iff] at this
      replace := Nat.mod_eq_of_modEq this pp.pos
      simp only [Nat.one_mod_eq_zero_iff] at this
      linarith only [this, pp.one_lt]
    have h6: (p:ℤ) = p / ((p:ℤ).gcd (a^(m.gcd n))) := by
      rw [Int.isCoprime_iff_gcd_eq_one] at h5
      simp [h5]
    rw [h6]
    refine Int.ModEq.cancel_right_div_gcd ?_ h4
    simp [pp.pos]

  -- if p is odd prime and p mod 8 not 1, then gcd (p-1,8) is 2 or 4
  have gcd_p1_8 {p:ℕ} (pp: Nat.Prime p) (podd: Odd p)
    (p_not_dvd: ¬ 8 ∣ p-1): Nat.gcd (p-1) 8 = 2 ∨ Nat.gcd (p-1) 8 = 4 := by
    -- divisor of 8 is 1,2,4,8.
    have h1: ∀(d:ℕ), d ∣ 8 → d=1 ∨ d=2 ∨ d=4 ∨ d=8 := by
      intro d hdvd
      have := Nat.le_of_dvd (by norm_num) hdvd
      revert hdvd
      clear * - this
      decide +revert
    -- p is odd, then p-1 is even, divided by 2.
    have h2: 2 ∣ p-1 := by
      rw [← even_iff_two_dvd]
      apply Nat.Odd.sub_odd podd (by norm_num)
    by_cases h3: 4 ∣ p-1
    · right; symm
      apply Nat.gcd_greatest h3 (by norm_num)
      intro d hd1 hd2
      replace hd2 := h1 d hd2
      rcases hd2 with (rfl | rfl | rfl | rfl)
      any_goals contradiction
      all_goals norm_num
    · left; symm
      apply Nat.gcd_greatest h2 (by norm_num)
      intro d hd1 hd2
      replace hd2 := h1 d hd2
      rcases hd2 with (rfl | rfl | rfl | rfl)
      any_goals contradiction
      all_goals norm_num


  -- for odd prime p, p mod 8 ≠ 1, then p ∣ x^4+y^4 leads to p ∣ x, p ∣ y.
  have aux2 {x y p: ℕ} (pp: Nat.Prime p) (p_not_dvd: ¬ 8 ∣ p-1) (podd: Odd p)
    (hdvd: p ∣ x^4+y^4): p ∣ x ∧ p ∣ y := by
    -- x^8 - y^8 = (x^4+y^4)(x^4-y^4), so p divide x^8 - y^8
    have h1: (p:ℤ) ∣ x^8 - y^8 := by
      have: (x^8:ℤ) - y^8 = (x^4+y^4)*(x^4-y^4) := by ring
      rw [this]
      apply Dvd.dvd.mul_right ?_
      exact Int.ofNat_dvd_left.mpr hdvd

    -- if one of them divided by p, done.
    by_cases hx: p ∣ x
    · have h2: (p:ℤ) ∣ x^8 := by
        zify at hx
        refine Dvd.dvd.pow hx (by norm_num)
      have h3: p ∣ y^8 := by
        zify
        exact (Int.dvd_iff_dvd_of_dvd_sub h1).mp h2
      have hy: p ∣ y := Nat.Prime.dvd_of_dvd_pow pp h3
      exact ⟨hx,hy⟩
    by_cases hy: p ∣ y
    · have h2: (p:ℤ) ∣ y^8 := by
        zify at hy
        apply Dvd.dvd.pow hy (by norm_num)
      have: p ∣ x^8 := by
        zify
        exact (Int.dvd_iff_dvd_of_dvd_sub h1).mpr h2
      absurd hx
      exact Nat.Prime.dvd_of_dvd_pow pp this

    -- else, both are coprime to p.
    replace hx := (pp.coprime_iff_not_dvd.mpr hx).symm
    replace hy :=(pp.coprime_iff_not_dvd.mpr hy).symm

    -- by Fermat's little theorem, p divide x^(p-1) - y^(p-1)
    have h2: (p:ℤ) ∣ x^(p-1) - y^(p-1) := by
      rw [← Nat.isCoprime_iff_coprime] at hx hy
      refine Int.ModEq.dvd ?_
      have h2: (x:ℤ)^(p-1) ≡ 1 [ZMOD p] := by
        exact Int.ModEq.pow_card_sub_one_eq_one pp hx
      have h3: (y:ℤ)^(p-1) ≡ 1 [ZMOD p] := by
        exact Int.ModEq.pow_card_sub_one_eq_one pp hy
      exact h3.trans h2.symm

    -- then we claim x^d ≡ y^d (mod p), where d is gcd of 8 and p-1.
    have h3: (p:ℤ) ∣ x^((p-1).gcd 8) - y^((p-1).gcd 8) := by
      rw [← Int.modEq_iff_dvd] at h1 h2 ⊢
      apply aux1 h2 h1 hy hx pp

    -- it suffices to show p divide x^4-y^4
    suffices (p:ℤ) ∣ x^4-y^4 by
      replace: (p:ℤ) ∣ 2*x^4 := by
        have hh: (2:ℤ)*x^4 = (x^4+y^4) + (x^4-y^4) := by ring
        rw [hh]
        zify at hdvd
        refine (Int.dvd_add_right hdvd).mpr this
      norm_cast at this
      rw [← Nat.coprime_two_right] at podd
      rw [Nat.Coprime.dvd_mul_left podd] at this
      have pdvdx: p ∣ x := pp.dvd_of_dvd_pow this
      replace: p ∣ y^4 := (Nat.dvd_add_iff_right this).mpr hdvd
      have pdvdy: p ∣ y := pp.dvd_of_dvd_pow this
      exact ⟨pdvdx, pdvdy⟩

    -- and gcd of p-1 and 8 is 2 or 4, either case we can prove p divide x^4-y^4.
    specialize gcd_p1_8 pp podd p_not_dvd
    rcases gcd_p1_8 with (d2 | d4)
    · have: (x:ℤ)^4 - y^4 = (x^2-y^2)*(x^2+y^2) := by ring
      rw [d2] at h3
      rw [this]
      apply Dvd.dvd.mul_right h3
    · rwa [d4] at h3

  -- back to the problem.
  constructor

  · -- verify 481 is possible.
    simp only [Set.mem_setOf_eq]
    -- let x=y=481
    use 481,481
    simp only [← and_assoc]
    refine ⟨(by norm_num), ?_⟩
    -- take a = 31 × 481, b = 481.
    use (31*481),481
    norm_num

  · -- prove such x,y ≥ 481.
    simp only [lowerBounds, Set.mem_setOf_eq, forall_exists_index, and_imp]
    rintro u x y rfl xpos ypos a b ha hb
    -- y is positive, so 15b < 16a
    have h1: 15*b < 16*a := by
      refine Nat.lt_of_sub_pos ?_
      simp [hb, ypos]
    -- notice that x^4 + y^4 = (x^2)^2 + (y^2)^2 = (15^2+16^2)(a^2+b^2)
    have h2: x^4 + y^4 = (15^2+16^2)*(a^2+b^2) := by
      have: 4 = 2*2 := by norm_num
      rw [this, pow_mul, pow_mul, ← ha, ← hb]
      zify
      rw [Nat.cast_sub h1.le]
      push_cast
      ring
    -- 15^2+16^2 = 481 = 13 x 37, so 13,37 divide x^4+y^4,
    -- therefore divide x and y
    have odd13: Odd 13 := Nat.odd_iff.mpr rfl
    have odd37: Odd 37 := Nat.odd_iff.mpr rfl
    have h3: 13 ∣ x ∧ 13 ∣ y := by
      have: 13 ∣ x^4+y^4 := by
        rw [h2]
        apply Dvd.dvd.mul_right (by norm_num)
      refine aux2 ?_ ?_ odd13 this
      <;> norm_num
    have h4: 37 ∣ x ∧ 37 ∣ y := by
      have: 37 ∣ x^4+y^4 := by
        rw [h2]
        apply Dvd.dvd.mul_right (by norm_num)
      refine aux2 ?_ ?_ odd37 this
      <;> norm_num
    -- then 13 x 37 = 481 divide x,y
    have hx: 13*37 ∣ x := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h3.left h4.left
    have hy: 13*37 ∣ y := by
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl h3.right h4.right
    -- thus both x,y ≥ 481.
    norm_num at hx hy
    apply le_min
    all_goals
      apply Nat.le_of_dvd
      <;> assumption
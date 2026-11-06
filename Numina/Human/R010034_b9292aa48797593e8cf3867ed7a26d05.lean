import Mathlib

/-Find all the triplets (p, q, r) of prime numbers such that the 3 differences
|p - q|, |q - r|, |r - p|
are also prime numbers.-/

theorem number_theory_607293: {(p, q, r): ℤ × ℤ × ℤ | 0 < p ∧ 0 < q ∧ 0 < r ∧
Prime |p - q| ∧ Prime |q - r| ∧ Prime |r - p| ∧ Prime p ∧ Prime q ∧ Prime r}
= {(2,5,7), (2,7,5), (5,2,7), (5,7,2), (7,2,5), (7,5,2)} := by

  -- For simplicity, we will first prove the case when p < q < r
  have h_cases: ∀ x y z: ℤ, 0 < x ∧ x < y ∧ y < z ∧
  Prime |x - y| ∧ Prime |y - z| ∧ Prime |z - x| ∧ Prime x ∧ Prime y ∧ Prime z → (x, y, z) = (2, 5, 7) := by

    -- we first prove a lemma which be used many times
    have h_not: ¬ ∃ k: ℕ, Nat.Prime k ∧ Nat.Prime (k + 2) ∧ Nat.Prime (k + 4) ∧ k ≠ 3 := by
      by_contra! h
      obtain ⟨k, h⟩ := h
      rcases h with ⟨h1,h2,h3,hk⟩
      have case: 3 ∣ k ∨ 3 ∣ k + 1 ∨ 3 ∣ k + 2 := by omega
      rcases case with l | l | l
      . rw [Nat.Prime.dvd_iff_eq] at l
        tauto
        exact h1
        norm_num
      . have o: 3 ∣ k + 4 := by omega
        rw [Nat.Prime.dvd_iff_eq] at o
        omega
        exact h3
        norm_num
      . have o: 3 ∣ k + 2 := by omega
        rw [Nat.Prime.dvd_iff_eq] at o
        replace o: k = 1 := by omega
        rw [o] at h1
        absurd h1
        norm_num
        exact h2
        norm_num

    intro x y z
    intro h
    rcases h with ⟨lx,ly,lz,hxy,hyz,hzx,hx,hy,hz⟩
    simp
    -- for convenience, we turn x y z into natural numbers
    rw [Int.prime_iff_natAbs_prime] at *
    set p:= x.natAbs with hp
    set q:= y.natAbs with hq
    set r:= z.natAbs with hr
    have exy: |x - y|.natAbs = q - p := by
      have o: |x - y| = - (x - y) := by
        apply abs_of_nonpos
        linarith
      simp [o]
      simp [hp, hq]
      rw [Int.natAbs_eq_iff]
      left
      rw [show ↑(y.natAbs - x.natAbs) = (y.natAbs: ℤ) - (x.natAbs: ℤ) by apply Int.natCast_sub; omega]
      rw [← Int.eq_natAbs_of_zero_le]
      rw [← Int.eq_natAbs_of_zero_le ]
      omega
      omega
    have eqy: |y - z|.natAbs = r - q := by
      have o: |y - z| = - (y - z) := by
        apply abs_of_nonpos
        linarith
      simp [o]
      simp [hq, hr]
      rw [Int.natAbs_eq_iff]
      left
      rw [show ↑(z.natAbs - y.natAbs) = (z.natAbs: ℤ) - (y.natAbs: ℤ) by apply Int.natCast_sub; omega]
      rw [← Int.eq_natAbs_of_zero_le]
      rw [← Int.eq_natAbs_of_zero_le ]
      omega
      omega
    have eqz: |z - x|.natAbs = r - p := by
      have o: |z - x| = (z - x) := by
        apply abs_of_nonneg
        linarith
      simp [o]
      simp [hr, hp]
      rw [Int.natAbs_eq_iff]
      left
      rw [show ↑(z.natAbs - x.natAbs) = (z.natAbs: ℤ) - (x.natAbs: ℤ) by apply Int.natCast_sub; omega]
      rw [← Int.eq_natAbs_of_zero_le]
      rw [← Int.eq_natAbs_of_zero_le ]
      omega
      omega
    simp [exy, eqy, eqz] at hxy hyz hzx
    clear exy eqy eqz
    have lpq: p < q := by
      simp [hp, hq]
      zify
      rw [show |x| = x by apply abs_of_nonneg; omega]
      rw [show |y| = y by apply abs_of_nonneg; omega]
      omega
    have lqr: q < r := by
      simp [hq, hr]
      zify
      rw [show |y| = y by apply abs_of_nonneg; omega]
      rw [show |z| = z by apply abs_of_nonneg; omega]
      omega
    replace ly: 0 < y := by omega
    replace lz: 0 < z := by omega
    clear_value p q r
    -- Then we show that p = 2, q = 5, r = 7
    have h_val: p = 2 ∧ q = 5 ∧ r = 7 := by
      clear lx ly lz
      by_cases lp: p = 2
      -- for the case p = 2
      . have or: Odd r := by
          apply Nat.Prime.odd_of_ne_two
          exact hz
          omega
        have oq: Odd q := by
          apply Nat.Prime.odd_of_ne_two
          exact hy
          omega
        have eqr: Even (r - q) := by
          apply Odd.tsub_odd
          exact or
          exact oq
        rw [Nat.Prime.even_iff] at eqr
        replace eqr: r = q + 2 := by omega
        rw [eqr] at hz
        rw [lp] at hxy
        have lq: 2 < q := by omega
        by_cases lq: q = 5
        -- for the case q = 5, it gives the only solution
        . omega
        -- for the case q ≠ 5
        absurd h_not
        use (q - 2)
        constructor
        . exact hxy
        . constructor
          . rw [show q - 2 + 2 = q by omega]
            exact hy
          . constructor
            . rw [show q - 2 + 4 = q + 2 by omega]
              exact hz
            . omega
        exact hyz
      -- for the case p ≠ 2
      . replace lp: 3 ≤ p := by
          by_contra! no
          interval_cases p
          all_goals absurd hx; norm_num
          tauto
        have op: Odd p := by
          apply Nat.Prime.odd_of_ne_two
          exact hx
          omega
        have oq: Odd q := by
          apply Nat.Prime.odd_of_ne_two
          exact hy
          omega
        have or: Odd r := by
          apply Nat.Prime.odd_of_ne_two
          exact hz
          omega
        have eqp: Even (q - p) := by
          apply Odd.tsub_odd
          exact oq
          exact op
        rw [Nat.Prime.even_iff] at eqp
        have erq: Even (r - q) := by
          apply Odd.tsub_odd
          exact or
          exact oq
        rw [Nat.Prime.even_iff] at erq
        replace eqp: q = p + 2 := by omega
        replace erq: r = q + 2 := by omega
        rw [eqp] at hy
        rw [erq] at hz
        simp [eqp] at hz
        rw [show p + 2 + 2 = p + 4 by omega] at hz
        absurd h_not
        use p
        by_cases ip: p = 3
        -- for the case p = 3
        . simp [hz,hy,hx]
          absurd hzx
          simp [erq,eqp,ip]
          norm_num
        -- for the case p ≠ 3
        . simp [hz,hy,hx,ip]
        exact hyz
        exact hxy

    simp [hp, hq, hr] at h_val
    zify at h_val
    rw [show |x| = x by apply abs_of_nonneg; omega] at h_val
    rw [show |y| = y by apply abs_of_nonneg; omega] at h_val
    rw [show |z| = z by apply abs_of_nonneg; omega] at h_val
    simp [h_val]


-- Now we can use this lemma to prove the main theorem
  ext ⟨p,q,r⟩
  constructor
  -- the forward direction
  intro h
  simp at h
  rcases h with ⟨lp,lq,lr,hpq,hqr,hrp,hp,hq,hr⟩
  have nepq: p ≠ q := by
    by_contra! no
    simp [no] at hpq
  have neqr: q ≠ r := by
    by_contra! no
    simp [no] at hqr
  have nerp: r ≠ p := by
    by_contra! no
    simp [no] at hrp
  have l_case: p < q ∧ q < r ∨ p < r ∧ r < q ∨ q < p ∧ p < r ∨
  q < r ∧ r < p ∨ r < p ∧ p < q ∨ r < q ∧ q < p := by omega
  rcases l_case with l | l | l | l | l | l
  -- the case p < q < r
  . rcases l with ⟨l1,l2⟩
    specialize h_cases p q r
    simp [*] at h_cases
    simp [h_cases]
  -- the case p < r < q
  . rcases l with ⟨l1,l2⟩
    specialize h_cases p r q
    simp [*] at h_cases
    replace hrp: Prime |p - r| := by
      have o: |p - r| = |r - p| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hrp]
    replace hpq: Prime |q - p| := by
      have o: |q - p| = |p - q| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hpq]
    replace hqr: Prime |r - q| := by
      have o: |r - q| = |q - r| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hqr]
    simp [*] at h_cases
    simp [h_cases]
  -- the case q < p < r
  . rcases l with ⟨l1,l2⟩
    specialize h_cases q p r
    simp [*] at h_cases
    replace hrp: Prime |p - r| := by
      have o: |p - r| = |r - p| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hrp]
    replace hpq: Prime |q - p| := by
      have o: |q - p| = |p - q| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hpq]
    replace hqr: Prime |r - q| := by
      have o: |r - q| = |q - r| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hqr]
    simp [*] at h_cases
    simp [h_cases]
  -- the case q < r < p
  . rcases l with ⟨l1,l2⟩
    specialize h_cases q r p
    simp [*] at h_cases
    simp [h_cases]
  -- the case r < p < q
  . rcases l with ⟨l1,l2⟩
    specialize h_cases r p q
    simp [*] at h_cases
    simp [h_cases]
  -- the case r < q < p
  . rcases l with ⟨l1,l2⟩
    specialize h_cases r q p
    simp [*] at h_cases
    replace hrp: Prime |p - r| := by
      have o: |p - r| = |r - p| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hrp]
    replace hpq: Prime |q - p| := by
      have o: |q - p| = |p - q| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hpq]
    replace hqr: Prime |r - q| := by
      have o: |r - q| = |q - r| := by
        rw [abs_eq_iff_mul_self_eq]
        ring
      simp [o,hqr]
    simp [*] at h_cases
    simp [h_cases]


  -- the backward direction
  . clear h_cases
    intro h
    simp only [Set.mem_setOf_eq]
    simp at h
    rcases h with h | h | h | h | h | h
    all_goals simp [h]; norm_num
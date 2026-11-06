import Mathlib


/- Find all integers $n>1$ such that any prime divisor of $n^{6}-1$
is a divisor of $\left(n^{3}-1\right)\left(n^{2}-1\right)$. -/


theorem number_theory_236678 (n : ℕ) (hn : n > 1) :
    ((n^6-1).primeFactors ⊆ ((n^3-1)*(n^2-1)).primeFactors) ↔ n = 2 := by

  -- n^6-1 = (n^2-n+1)(n+1)(n^3-1)
  have h1: (n^6-1:ℤ) = (n^2-n+1)*(n+1)*(n^3-1) := by ring
  replace h1: n^6 - 1 = (n^2-n+1)*(n+1)*(n^3-1) := by
    zify
    have: 1 ≤ n^6 := Nat.one_le_pow _ _ (by omega)
    rw [Nat.cast_sub this]
    push_cast
    rw [h1]
    congr
    · rw [Nat.cast_sub (Nat.le_self_pow (by norm_num) n)]
      simp
    · rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
      simp
  have h1': n^6-1 ≠ 0 := by
    have: 1 < n^6 := Nat.one_lt_pow (by norm_num) hn
    omega

  -- n^3+1 = (n^2-n+1)(n+1)
  have h2: (n^3+1:ℤ) = (n^2-n+1)*(n+1) := by ring
  replace h2: n^3+1 = (n^2-n+1)*(n+1) := by
    zify; rw [h2]
    congr 2
    rw [Nat.cast_sub (Nat.le_self_pow (by norm_num) _)]
    simp

  constructor

  · intro h

    -- any odd prime p divide n^2-n+1, p = 3.
    have h3 {p:ℕ} (pp: Nat.Prime p) (pne2: p ≠ 2)
      (hp: p ∣ n^2-n+1):
      p = 3 := by
      -- p divide n^3+1
      have hh1: p ∣ n^3+1 := by
        rw [h2]
        exact Dvd.dvd.mul_right hp (n + 1)
      -- then p not divide n^3-1
      have hh2: ¬ p ∣ n^3-1 := by
        rintro dvd
        have: n^3+1 = n^3-1 + 2 := by
          simp only [add_left_inj]
          rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))]
        rw [this] at hh1
        replace: p ∣ 2 := (Nat.dvd_add_iff_right dvd).mpr hh1
        absurd pne2
        apply le_antisymm
          (Nat.le_of_dvd (by norm_num) this) pp.two_le
      -- thus p divide n^2-1
      have hh3: p ∣ n^2-1 := by
        have: p ∈ (n^6-1).primeFactors := by
          simp only [Nat.mem_primeFactors, pp, ne_eq, h1',
          not_false_eq_true, and_true, true_and]
          rw [h1, mul_assoc]
          apply Dvd.dvd.mul_right hp
        replace := h this
        rw [Nat.mem_primeFactors,
        Nat.Prime.dvd_mul pp] at this
        tauto
      -- therefore p divide n^2(n+1)
      have hh4: p ∣ n^2 * (n+1) := by
        have: n^2*(n+1) = (n^3+1) + (n^2-1) := by
          rw [Nat.mul_add_one, ← pow_succ, add_assoc]
          rw [Nat.add_sub_of_le (Nat.one_le_pow _ _ (by omega))]
        rw [this]
        exact (Nat.dvd_add_iff_right hh1).mp hh3
      -- p divide n+1, since p cannot divide n^2
      have hh5: p ∣ n+1 := by
        rw [Nat.Prime.dvd_mul pp] at hh4
        rcases hh4 with hh | hh
        · have hh5: p ∣ (n^2-1).gcd (n^2) := by
            exact Nat.dvd_gcd hh3 hh
          have hh6: (n^2-1).gcd (n^2) = 1 := by
            refine (Nat.coprime_self_sub_left ?_).mpr ?_
            · apply Nat.one_le_pow _ _ (by omega)
            · exact Nat.gcd_one_left (n ^ 2)
          rw [hh6] at hh5
          replace hh5 := Nat.le_of_dvd (by norm_num) hh5
          linarith only [hh5, pp.one_lt]
        · exact hh

      -- p divide (n^2-1) - (n^2-n+1) = n-2
      have hh6: p ∣ n-2 := by
        have: n^2-1 = (n^2-n+1) + (n-2) := by
          zify
          rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
          Nat.cast_sub (Nat.le_self_pow (by norm_num) _),
          Nat.cast_sub (by exact hn)]
          ring
        rw [this] at hh3
        exact (Nat.dvd_add_iff_right hp).mpr hh3
      -- hence p = 3.
      have: p ∣ 3 := by
        have: n+1 = (n-2) + 3 := by omega
        rw [this] at hh5
        exact (Nat.dvd_add_iff_right hh6).mpr hh5
      symm
      rwa [Nat.Prime.dvd_iff_eq (by norm_num) pp.ne_one] at this

    -- so n^2-n+1 = 3^r
    obtain ⟨r, hr⟩: ∃ (r:ℕ), n^2-n+1 = 3^r := by
      have: 0 < n^2-n+1 := Nat.zero_lt_succ _
      rcases (Nat.exists_eq_pow_mul_and_not_dvd this.ne'
        3 (by norm_num)) with ⟨r,b,hb,heq⟩
      have: b = 1 := by
        by_contra!
        rw [Nat.ne_one_iff_exists_prime_dvd] at this
        rcases this with ⟨p, pp, pdvd⟩
        have pdvd': p ∣ n^2-n+1 := by
          rw [heq]
          exact Dvd.dvd.mul_left pdvd (3 ^ r)
        -- if 2 not divide n^2-n+1, since n^2-n+1 is odd.
        have pne2: p ≠ 2 := by
          have: Odd (n^2-n+1) := by
            have hh1: n^2-n+1 = n*(n-1) + 1 := by
              rw [Nat.mul_sub, ← pow_two, mul_one]
            have hh2: Even (n*(n-1)) := by
              exact Nat.even_mul_pred_self n
            rw [hh1]
            exact Even.add_one hh2
          rintro rfl
          absurd this
          rw [Nat.not_odd_iff_even]
          exact (even_iff_exists_two_nsmul _).mpr pdvd'
        -- then p = 3, because n^2-n+1 only contain 3 as its prime factor.
        specialize h3 pp pne2 pdvd'
        -- contradiction.
        absurd hb
        apply Dvd.dvd.trans ?_ pdvd
        simp [h3]
      use r
      simp [heq, this]


    -- or, n^2 - n + (1-3^r) has integer solution
    have h4: (1:ℤ)*(n*n) + -1*n + (1-3^r) = 0 := by
      zify at hr
      rw [Nat.cast_sub (Nat.le_self_pow (by norm_num) _)] at hr
      push_cast at hr
      linarith only [hr]
    -- then discriminant is integer square, or,
    -- (2n-1)^2 = 4 3^r - 3 = 0.

    replace h4: 4*3^r - (3:ℤ) = (2*n-1)^2 := by
      rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)] at h4
      simp only [discrim, Int.reduceNeg, even_two,
      Even.neg_pow, one_pow, mul_one] at h4
      linarith only [h4]

    -- when r=0, n^2-n+1 = 1, contradiction.
    have hr0: r ≠ 0 := by
      rintro rfl
      simp only [pow_zero, add_left_eq_self] at hr
      have hh1: n < n^2 := by
        rwa [pow_two, Nat.lt_mul_self_iff]
      have hh2: n^2 = n := by
        nth_rw 2 [← add_zero n]
        simp [← hr, le_of_lt hh1]
      simp [hh2] at hh1

    -- then r ≥ 1, 4 3^r - 3 = 3 (4 3^(r-1) - 1)
    have h5: 4*3^r - (3:ℤ) = 3 * (4*3^(r-1) - 1) := by
      have: r = r-1+1 := by omega
      nth_rw 1 [this, pow_succ]
      ring

    -- 3 divide 4 3^(r-1) - 1, since it's a square.
    replace h5: 3 ∣ 4*3^(r-1) - (1:ℤ) := by
      have: 3 ∣ (2*n-1:ℤ)^2 := by
        rw [← h4, h5]
        apply Int.dvd_mul_right
      replace: 3 ∣ (2*n-1:ℤ) := by
        apply Prime.dvd_of_dvd_pow ?_ this
        exact Int.prime_three
      rcases this with ⟨k, hk⟩
      rw [h4, hk] at h5
      replace: (3*k)^2 = 3 * (3*k^2) := by ring
      rw [this] at h5
      simp only [mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false] at h5
      use (k^2)
      rw [h5]

    -- thus r = 1, otherwise 3 divide 1, impossible.
    replace hr: r = 1 := by
      by_contra! hr
      replace hr: r-1 ≠ 0 := by omega
      have hh1: (3:ℤ) ∣ 4*3^(r-1) := by
        exact Dvd.dvd.mul_left (dvd_pow_self 3 hr) 4
      have hh2: 3 ∣ (1:ℤ) := by
        exact (Int.dvd_iff_dvd_of_dvd_sub h5).mp hh1
      norm_num at hh2

    -- then we solve n = 2
    replace h4: (2*n-1:ℤ)^2 = 3^2 := by
      rw [← h4, hr]
      norm_num

    -- 2n-1 = 3, n = 2
    rw [sq_eq_sq₀ (by omega) (by norm_num)] at h4
    linarith only [h4]

  · -- verification
    rintro rfl
    norm_num
    clear * -
    -- 63 = 7x9 = 7 x 3^2, 21 = 7x3, both prime factors are 7,3.
    native_decide
import Mathlib

-- we show that if 1 < n is prime, then n = pq for 1 < p and 1 < q
lemma not_prime_is_prod (n: ℤ) (hn: 1 < n) (h: ¬ Prime n): ∃ p q, 1 < p ∧ 1 < q ∧ n = p * q := by
   rw [Int.prime_iff_natAbs_prime] at h
   rw [Nat.not_prime_iff_exists_dvd_ne] at h
   obtain ⟨m, dm, hm, nm⟩ := h
   use m
   use n.natAbs / m
   have o: m ≠ 0 := by
      by_contra! o
      simp [o] at dm
      simp [dm] at hn
   constructor
   .
    simp
    omega
   .
    constructor
    .
      simp
      rw [show |n| = n by apply abs_of_nonneg; linarith]
      qify
      rw [Rat.intCast_div]
      .
        apply Bound.one_lt_div_of_pos_of_lt
        .
          simp
          omega
        .
          simp
          apply Nat.le_of_dvd at dm
          zify at dm
          rw [show |n| = n by apply abs_of_nonneg; linarith] at dm
          zify at nm
          rw [show |n| = n by apply abs_of_nonneg; linarith] at nm
          norm_cast
          omega
          zify
          rw [show |n| = n by apply abs_of_nonneg; linarith]
          omega
      .
        zify at dm
        rw [show |n| = n by apply abs_of_nonneg; linarith] at dm
        exact dm
    .
      qify
      rw [Rat.intCast_div]
      .
        field_simp
        rw [show |(n: ℚ)| = n by apply abs_of_nonneg; simp; omega]
      .
        zify at dm
        exact dm

   zify
   rw [show |n| = n by apply abs_of_nonneg; omega]
   omega


/-Prove that the equation 1/x−1/y=1/n has a unique solution
in natural numbers if and only if n is a prime number.-/

theorem number_theory_199932 {n: ℤ} (ln: 1 < n):
  (∃ x y: ℤ, 0 < x ∧ 0 < y ∧ (1: ℚ) / x - 1 / y = 1 / n ∧
  (∀ x' y': ℤ, 0 < x'∧ 0 < y' ∧ (1: ℚ) / x' - 1 / y' = 1 / n → x' = x ∧ y' = y)) ↔ Prime n := by

  constructor

  -- the forward direction
  .
    intro h
    obtain ⟨x, y, hx, hy, h, h'⟩ := h
    by_contra! s
    apply not_prime_is_prod at s
    obtain ⟨p, q, hp, hq, hn⟩ := s

    -- then we show that there are two solutions
    have h1:= h' (n - 1) (n * (n - 1))  -- the first solution
    simp at h1
    simp [ln] at h1
    have o1: 0 < n := by omega
    simp [o1] at h1
    field_simp at h1
    have o2: ((1: ℚ) / (↑n - 1) - 1 / ((↑n - 1) * ↑n)) * ↑n = 1 := by
      have n1: n - (1: ℚ) ≠ 0 := by
        by_contra! o
        norm_cast at o
        omega
      have n2: n * (n - (1: ℚ)) ≠ 0 := by
        by_contra! s
        simp at s
        norm_cast at s
        omega
      field_simp
    simp only [o2] at h1
    field_simp at h1
    clear o1 o2

    have h2:= h' (p * (q - 1)) (p * q * (q - 1))  --the second solution
    clear h'
    have o1: 0 < p * (q - 1) := by
      nlinarith
    simp [o1] at h2
    have o2: 0 < p * q * (q - 1) := by
      nlinarith
    have o3: (q - (1: ℚ)) * p ≠ 0 := by
      by_contra! o
      simp at o
      norm_cast at o
      omega
    have o4: (q - (1: ℚ)) * (q * p) ≠ 0 := by
      by_contra! o
      simp at o
      norm_cast at o
      omega
    simp [o2] at h2
    field_simp at h2
    rw [hn] at h2
    rw [show ↑(p * q) = (p: ℚ) * q by simp] at h2
    ring_nf at h2
    simp at h2

    -- use h1 and h2 to get a contradiction
    rcases h1 with ⟨f1, f2⟩
    rcases h2 with ⟨g1, g2⟩
    rw [hn] at f1 f2
    rw [← g1] at f1
    rw [← g2] at f2
    nlinarith [f1]
    exact ln


  -- the backward direction
  .
    intro h
    use (n - 1)
    use (n * (n - 1))
    have o1: 0 < n - 1 := by
      nlinarith
    simp [o1]
    have o2: 0 < n := by
      omega
    simp [o2]
    field_simp
    constructor
    .
      have n1: n - (1: ℚ) ≠ 0 := by
        by_contra! o
        norm_cast at o
        omega
      have n2: (n - (1: ℚ)) * n ≠ 0 := by
        by_contra! s
        simp at s
        norm_cast at s
        omega
      field_simp
    .
      intro x y hx hy h
      field_simp at h
      norm_cast at h
      have d: n ∣ x * y := by
        rw [← h]
        simp
      rw [Prime.dvd_mul] at d
      have ox: x < n := by
        nlinarith
      rcases d with d | d
      .
        apply exists_eq_mul_right_of_dvd at d
        obtain ⟨k, hk⟩ := d
        have vk: 0 < k := by nlinarith
        have uk: k < 1 := by nlinarith
        omega
      .
        apply exists_eq_mul_left_of_dvd at d
        obtain ⟨k, hk⟩ := d
        simp [hk] at h
        replace h: k * n = (k + 1) * x := by nlinarith
        have lk: 0 < k := by nlinarith
        -- we show that n = k + 1
        have d: k + 1 ∣ k * n := by
          rw [h]
          simp
        apply IsCoprime.dvd_of_dvd_mul_left at d
        .
          rw [← Int.natAbs_dvd_natAbs] at d
          rw [Nat.Prime.dvd_iff_eq] at d
          zify at d
          rw [show |n| = n by apply abs_of_nonneg; linarith] at d
          rw [show |k + 1| = k + 1 by apply abs_of_nonneg; linarith] at d
          rw [d] at h
          replace h: x = k := by nlinarith
          replace h: x = n - 1 := by omega
          simp [h]
          replace d: k = n - 1 := by nlinarith
          rw [d] at hk
          simp [hk]
          ring
          rw [← Int.prime_iff_natAbs_prime]
          trivial
          zify
          rw [show |k + 1| = k + 1 by apply abs_of_nonneg; linarith]
          omega
        .
          rw [show k + 1 = 1 + 1 * k by ring]
          apply IsCoprime.add_mul_right_left
          apply isCoprime_one_left
      trivial

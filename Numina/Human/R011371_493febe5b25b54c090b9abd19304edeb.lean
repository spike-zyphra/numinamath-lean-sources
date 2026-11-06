import Mathlib

-- we show a key division lemma
lemma lemma_1 (x y: ℕ) (l: y < x) (h: x ^ y = y ^ x): y ∣ x := by
  have ly: 0 < y := by
    by_contra! o
    replace o: y = 0 := by omega
    simp [o] at h
    rw [Nat.zero_pow_of_pos] at h
    trivial
    omega
  set d:= x.gcd y
  have ld: 0 < d := by
    apply Nat.gcd_pos_of_pos_left
    omega
  have dx: d ∣ x := by
    simp [d]
    apply Nat.gcd_dvd_left
  have dy: d ∣ y := by
    simp [d]
    apply Nat.gcd_dvd_right
  apply exists_eq_mul_right_of_dvd at dx
  obtain ⟨a, ha⟩ := dx
  apply exists_eq_mul_right_of_dvd at dy
  obtain ⟨b, hb⟩ := dy

  -- then a and b are coprime
  have cp: Nat.Coprime a b := by
    have i: a = x / d := by
      rw [ha]
      symm
      apply Nat.mul_div_cancel_left
      exact ld
    have j: b = y / d := by
      rw [hb]
      symm
      apply Nat.mul_div_cancel_left
      exact ld
    rw [i, j]
    simp [d]
    apply Nat.coprime_div_gcd_div_gcd
    simp [d] at ld
    exact ld

  rw [show x ^ y = (a * d) ^ y by rw [ha]; ring] at h
  rw [show y ^ x = (b * d) ^ x by rw [hb]; ring] at h
  rw [show (a * d) ^ y = a ^ y * d ^ y by ring] at h
  rw [show (b * d) ^ x = b ^ x * d ^ x by ring] at h
  have f: d ^ x = d ^ y * d ^ (x - y) := by
    nth_rewrite 1 [show x = y + (x - y) by omega]
    ring
  rw [f] at h
  clear f
  have s: 0 < d ^ y := by
    apply Nat.pow_pos
    exact ld
  replace h: a ^ y = b ^ x * d ^ (x - y) := by
    nlinarith

  -- then we deduce b = 1 by the following division
  have u: b ∣ a ^ y := by
    rw [h]
    have o1: b ^ x ∣ b ^ x * d ^ (x - y) := by
      simp
    have o2: b ∣ b ^ x := by
      rw [show x = 1 + (x - 1) by omega]
      rw [show b ^ (1 + (x - 1)) = b * b ^ (x - 1) by ring]
      simp
    apply dvd_trans o2 o1
  replace cp: Nat.Coprime (a ^ y) b := by
    apply Nat.Coprime.pow_left
    exact cp
  apply Nat.Coprime.symm at cp
  have i:= Nat.Coprime.eq_one_of_dvd cp u
  simp [i] at hb
  simp [← hb] at ha
  simp [ha]

-- we show an inequality lemma will be used later
lemma lemma_2 (y k: ℕ) (ly: 2 ≤ y) (lk: 3 ≤ k): k < y ^ (k - 1) := by
  suffices p: k < 2 ^ (k - 1) by {
    have o: 2 ^ (k - 1) ≤ y ^ (k - 1) := by
      apply Nat.pow_le_pow_of_le_left
      omega
    nlinarith [p, o]
  }

  -- prove by induction on k
  induction' k with k ih
  .
    simp
  .
    by_cases l: k < 3
    .
      interval_cases k
      .
        simp at lk
      .
        simp at lk
      .
        norm_num
    .
      simp at l
      simp [l] at ih
      rw [show k + 1 - 1 = k - 1 + 1 by omega]
      rw [Nat.pow_succ]
      nlinarith


/-Solve the equation in the set of natural numbers
x ^ y = y ^ x (x ≠ y)-/

theorem number_theory_191070: {(x, y): ℕ × ℕ | x ≠ y ∧ x ^ y = y ^ x} = {(2, 4), (4, 2)} := by
  ext ⟨x, y⟩
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    rcases h with ⟨ne, h⟩
    by_cases l: y < x
    .
      have d:= lemma_1 x y l h
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, hk⟩ := d
      simp [hk] at h
      have ly: 0 < y := by
        by_contra! o
        replace o: y = 0 := by omega
        simp [o] at hk
        omega
      rw [show y ^ (y * k) = (y ^ k) ^ y by ring] at h
      rw [pow_left_inj₀] at h
      have lk: 0 < k := by
        by_contra! o
        replace o: k = 0 := by omega
        simp [o] at h
      have f: y ^ k = y * y ^ (k - 1) := by
        nth_rewrite 1 [show k = 1 + (k - 1) by omega]
        ring
      rw [f] at h
      clear f
      replace h: y ^ (k - 1) = k := by nlinarith
      by_contra! s

      -- we show that k is at least 3
      have u: 3 ≤ k := by
          by_contra! t
          replace t: k = 1 ∨ k = 2:= by omega
          rcases t with t | t
          .
            simp [t] at hk
            simp [hk] at ne
          .
            simp [t] at h
            simp [h, t] at hk
            simp [hk, h] at s

      -- use lemma 2, we can show that y ≤ 3
      have ry: y < 4 := by
        by_contra! o
        have j:= lemma_2 y k (by omega)

        simp [u] at j
        rw [h] at j
        simp at j

      interval_cases y
      .
        simp at h
        simp [← h] at hk
        simp [hk] at ne
      .
        have q:= lemma_2 2 k (by omega) (by omega)
        rw [h] at q
        simp at q
      .
        have q:= lemma_2 3 k (by omega) (by omega)
        rw [h] at q
        simp at q

      omega
      apply pow_nonneg
      omega
      omega

    -- case when x < y, just similarly
    .
      symm at h
      have d:= lemma_1 y x (by omega) h
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨k, hk⟩ := d
      simp [hk] at h
      have lx: 0 < x := by
        by_contra! o
        replace o: x = 0 := by omega
        simp [o] at hk
        omega
      rw [show x ^ (x * k) = (x ^ k) ^ x by ring] at h
      rw [pow_left_inj₀] at h
      have lk: 0 < k := by
        by_contra! o
        replace o: k = 0 := by omega
        simp [o] at h
      have f: x ^ k = x * x ^ (k - 1) := by
        nth_rewrite 1 [show k = 1 + (k - 1) by omega]
        ring
      rw [f] at h
      clear f
      replace h: x ^ (k - 1) = k := by nlinarith
      by_contra! s

      -- we show that k is at least 3
      have u: 3 ≤ k := by
          by_contra! t
          replace t: k = 1 ∨ k = 2:= by omega
          rcases t with t | t
          .
            simp [t] at hk
            simp [hk] at ne
          .
            simp [t] at h
            simp [h, t] at hk
            simp [hk, h] at s

      -- use lemma 2, we can show that y ≤ 3
      have rx: x < 4 := by
        by_contra! o
        have j:= lemma_2 x k (by omega) (by omega)

        simp [u] at j
        rw [h] at j
        simp at j

      interval_cases x
      .
        simp at h
        simp [← h] at hk
        simp [hk] at ne
      .
        have q:= lemma_2 2 k (by omega) (by omega)
        rw [h] at q
        simp at q
      .
        have q:= lemma_2 3 k (by omega) (by omega)
        rw [h] at q
        simp at q

      omega
      apply pow_nonneg
      omega
      omega


  -- the backward direction.
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
    .
      simp [h]
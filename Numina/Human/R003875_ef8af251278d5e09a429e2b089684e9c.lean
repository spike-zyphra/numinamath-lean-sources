import Mathlib

-- we write the process to solve the equation as a lemma
lemma lemma_1 (b c: ℕ) (lb: b < 10) (lc: c < 10) (h: b ^ 2 - c ^ 2 = 24):
  b = 7 ∧ c = 5 ∨ b = 5 ∧ c = 1 := by
  have r: c ^ 2 ≤ b ^ 2 := by omega
  have l: c ≤ b := by
    rw [Nat.pow_le_pow_iff_left] at r
    exact r
    norm_num

  -- we show the sq formula for b and c
  have s: b ^ 2 - c ^ 2 = (b + c) * (b - c) := by
    zify
    have i1: ↑(b ^ 2 - c ^ 2) = (b ^ 2: ℤ) - (c ^ 2: ℤ) := by
      apply Int.natCast_sub r
    have i2: ↑(b - c) = (b: ℤ) - (c: ℤ) := by
      apply Int.natCast_sub l
    rw [i1, i2]
    ring
  rw [s] at h
  clear s
  have p: b - c ≤ b + c := by
    omega
  have t: b - c < 5 := by nlinarith
  have f: b - c ∈ Nat.divisors 24 := by
    simp
    rw [← h ]
    simp
  rw [show Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} by native_decide] at f
  simp at f
  rcases f with f | f | f | f | f | f | f | f
  all_goals simp [f] at t
  all_goals simp [f] at h; omega

/-Determine all four-digit natural numbers divisible by 45
for which the difference of the squares of the hundreds digit and the tens digit is 24.-/

theorem number_theory_218117: {n: ℕ | ∃ a b c d, n = 1000 * a + 100 * b + 10 * c + d ∧
  0 < a ∧ a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10 ∧ 45 ∣ n ∧ (b ^2  - c ^ 2 = 24)} = {1755, 3510, 6750, 7515}:= by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp
    simp at h
    obtain ⟨a, b, c, d, hn, ra, la, lb, lc, ld, d1, h⟩ := h
    have i:= lemma_1 b c lb lc h
    clear h lb lc
    rcases i with i | i

    -- case b = 7 ∧ c = 5
    .
      simp [i] at *
      ring_nf at hn
      have t: 5 ∣ n := by
        have q: 5 ∣ 45 := by norm_num
        apply dvd_trans q d1

      -- first division relation to get d = 5 ∨ d = 10
      replace t: 5 ∣ d := by
        rw [show d = n - 5 * (150 + 200 * a) by rw [hn]; omega]
        apply Nat.dvd_sub
        .
          omega
        .
          exact t
        .
          simp
      apply exists_eq_mul_right_of_dvd at t
      obtain ⟨g, hg⟩ := t
      have lg: g < 2 := by nlinarith
      have rd: d = 0 ∨ d = 5 := by omega
      clear lg hg
      have s: 9 ∣ n := by
        have q: 9 ∣ 45 := by norm_num
        apply dvd_trans q d1
      rw [hn] at s

      -- second division relation
      replace s: 9 ∣ 3 + a + d := by
        rw [show 3 + a + d = 750 + a * 1000 + d - 9 * (83 + 111 * a) by omega]
        apply Nat.dvd_sub
        .
          omega
        .
          exact s
        .
          simp
      apply exists_eq_mul_right_of_dvd at s
      obtain ⟨k, h⟩ := s
      clear d1
      have lk: k < 3 := by nlinarith
      interval_cases k

      -- k = 0
      .
        replace h: a + d = 6 := by omega
        rcases rd with rd | rd
        .
          simp [rd] at h
          simp [rd, h] at hn
          simp [hn]
        .
          simp [rd] at h
          simp [rd, h] at hn
          simp [hn]

      -- k = 1
      .
        replace h: a + d = 6 := by omega
        rcases rd with rd | rd
        .
          simp [rd] at h
          simp [rd, h] at hn
          simp [hn]
        .
          simp [rd] at h
          simp [rd, h] at hn
          simp [hn]

      -- k = 2
      .
        replace h: a + d = 15 := by omega
        rcases rd with rd | rd
        .
          simp [rd] at h
          simp [h] at la
        .
          simp [rd] at h
          simp [h] at la

    -- case b = 5 ∧ c = 1
    .
      simp [i] at *
      ring_nf at hn

      -- first division relation to get d = 0 ∨ d = 5
      have t: 5 ∣ n := by
        have q: 5 ∣ 45 := by norm_num
        apply dvd_trans q d1
      replace t: 5 ∣ d := by
        rw [show d = n - 5 * (102 + 200 * a) by rw [hn]; omega]
        apply Nat.dvd_sub
        .
          omega
        .
          exact t
        .
          simp
      apply exists_eq_mul_right_of_dvd at t
      obtain ⟨g, hg⟩ := t
      have lg: g < 2 := by nlinarith
      have rd: d = 0 ∨ d = 5 := by omega
      clear lg hg

      -- second division relation
      .
        have s: 9 ∣ n := by
          have q: 9 ∣ 45 := by norm_num
          apply dvd_trans q d1
        rw [hn] at s
        replace s: 9 ∣ 6 + a + d := by
          rw [show 6 + a + d = 510 + a * 1000 + d - 9 * (56 + 111 * a) by omega]
          apply Nat.dvd_sub
          .
            omega
          .
            exact s
          .
            simp
        apply exists_eq_mul_right_of_dvd at s
        obtain ⟨k, h⟩ := s
        clear d1
        have lk: k < 3 := by nlinarith
        interval_cases k

        -- k = 0
        .
          omega

        -- k = 1
        .
          replace h: a + d = 3 := by omega
          rcases rd with rd | rd
          .
            simp [rd] at h
            simp [h, rd] at hn
            simp [hn]
          .
            simp [rd] at h

        -- k = 2
        .
          replace h: a + d = 12 := by omega
          rcases rd with rd | rd
          .
            simp [rd] at h
            simp [h] at la
          .
            simp [rd] at h
            simp [h, rd] at hn
            simp [hn]


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h | h
    .
      simp [h]
      use 1, 7, 5, 5
      norm_num
    .
      simp [h]
      use 3, 5, 1, 0
      norm_num
    .
      simp [h]
      use 6, 7, 5, 0
      norm_num
    .
      simp [h]
      use 7, 5, 1, 5
      norm_num

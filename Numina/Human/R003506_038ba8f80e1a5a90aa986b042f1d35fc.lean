import Mathlib

-- we show a lemma to simpiify the division equation
lemma lemma_1 (x y z u: ℤ) (h: 11 ∣ x * 1000 + y * 100 + z * 10 + u): 11 ∣ (x + z) - (y + u) := by
    rw [show (x + z) - (y + u) = 11 * (91 * x + 9 * y + z) - (x * 1000 + y * 100 + z * 10 + u) by ring]
    apply dvd_sub
    .
      simp
    .
      tauto

/-Find such four-digit numbers, each of which is divisible by 11,
and the sum of the digits of each of them is 11.-/

theorem number_theory_189105: {n: ℤ | ∃ x y z u, 0 < x ∧ x < 10 ∧ 0 ≤ y ∧ y < 10 ∧ 0 ≤ z ∧ z < 10 ∧ 0 ≤ u ∧ u < 10 ∧
  n = x * 1000 + y * 100 + z * 10 + u ∧ 11 ∣ n ∧ x + y + z + u = 11}
  = {2090, 3080, 4070, 5060, 6050, 7040, 8030, 9020} := by

  ext n
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    obtain ⟨x, y, z, u, lx, rx, ly, ry, lz, rz, lu, ru, hn, h1, h2⟩ := h
    rw [hn] at h1

    -- we use lemma_1 to simplify the divisibility condition
    apply lemma_1 at h1
    apply exists_eq_mul_right_of_dvd at h1
    obtain ⟨k, h1⟩ := h1
    have lk: -2 < k := by omega
    have rk: k < 2 := by omega

    -- we check all cases for k
    interval_cases k

    -- k = -1
    .
      simp at h1
      have f1: x + z = 0 := by omega
      omega

    -- k = 0
    .
      simp at h1
      omega

    -- k = 1
    .
      simp at h1
      replace h1: z = 11 - x := by omega
      replace h2: y + u = 0 := by omega
      have vy: y = 0 := by omega
      have vu: u = 0 := by omega
      simp [vy, vu] at *
      simp [h1] at hn
      ring_nf at hn
      interval_cases x
      all_goals simp [hn]
      omega


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h | h | h | h
    .
      simp only [Set.mem_setOf_eq, h]
      use 2, 0, 9, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 3, 0, 8, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 4, 0, 7, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 5, 0, 6, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 6, 0, 5, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 7, 0, 4, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 8, 0, 3, 0
      norm_num
    .
      simp only [Set.mem_setOf_eq, h]
      use 9, 0, 2, 0
      norm_num
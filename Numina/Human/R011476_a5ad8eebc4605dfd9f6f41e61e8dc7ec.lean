import Mathlib

/-Find a three-digit number with distinct digits,
whose five times is the sum of the other three-digit numbers written with the same digits.
Determine all solutions!-/

theorem number_theory_248984: {n: ℤ | ∃ x y z, 0 < x ∧ x < 10 ∧ 0 < y ∧ y < 10 ∧ 0 < z ∧ z < 10 ∧
  x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ n = 100 * x + 10 * y + z ∧
  5 * n = (100 * x + 10 * z + y) + (100 * y + 10 * x + z) + (100 * y + 10 * z + x) +
  (100 * z + 10 * y + x) + (100 * z + 10 * x + y)} = {481, 518, 592, 629}:= by

    ext n
    constructor

    -- the forward direction
    .
      simp only [Set.mem_setOf_eq]
      intro h
      obtain ⟨x, y, z, lx, rx, ly, ry, lz, rz, hxy, hxz, hyz, hn, h⟩ := h
      simp
      rw [hn] at h
      ring_nf at h
      replace h: 378 * x = 162 * y + 216 * z := by nlinarith
      replace h: 7 * x = 3 * y + 4 * z := by nlinarith

      -- then we show the key equation
      replace h: 7 * (x - z) = 3 * (y - z) := by nlinarith

      have d: 7 ∣ y - z := by
        have o: 7 ∣ 7 * (x - z) := by
          simp
        rw [h] at o
        apply IsCoprime.dvd_of_dvd_mul_left at o
        exact o
        norm_num
      apply exists_eq_mul_right_of_dvd at d
      obtain ⟨c, s⟩ := d
      have lc: c ≤ 1 := by nlinarith
      have rc: -1 ≤ c := by nlinarith
      interval_cases c

      -- c = -1
      .
        simp at s
        simp [s] at h
        have lz: 8 ≤ z := by omega
        interval_cases z
        -- z = 8
        .
          replace s: y = 1 := by omega
          replace h: x = 5 := by omega
          simp [h, s] at hn
          simp [hn]
        -- z = 9
        .
          replace s: y = 2 := by omega
          replace h: x = 6 := by omega
          simp [h, s] at hn
          simp [hn]

      -- c = 0
      .
        replace s: y = z := by omega
        simp [s] at hyz

      -- c = 1
      .
        have lz: z ≤ 2 := by omega
        interval_cases z
        -- z = 1
        .
          replace s: y = 8 := by omega
          simp [s] at h
          replace h: x = 4 := by omega
          simp [h, s] at hn
          simp [hn]
        -- z = 2
        .
          replace s: y = 9 := by omega
          simp [s] at h
          replace h: x = 5 := by omega
          simp [h, s] at hn
          simp [hn]


    --the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h | h

      -- n = 481
      .
        rw [h]
        simp only [Set.mem_setOf_eq]
        use 4
        use 8
        use 1
        norm_num

      -- n = 518
      .
        rw [h]
        simp only [Set.mem_setOf_eq]
        use 5
        use 1
        use 8
        norm_num

      -- n = 592
      .
        rw [h]
        simp only [Set.mem_setOf_eq]
        use 5
        use 9
        use 2
        norm_num

      -- n = 629
      .
        rw [h]
        simp only [Set.mem_setOf_eq]
        use 6
        use 2
        use 9
        norm_num

import Mathlib

/- Find the number of positive integer solutions to n ^ x + n ^ y = n ^ z
with n ^ z < 2001-/

theorem number_theory_610846: {(x, y, z, n): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < n ∧ n ^ z < 2001 ∧
n ^ x + n ^ y = n ^ z}.encard = 9 := by

  -- we directly compute the set
  have h_eq: {(x, y, z, n): ℕ × ℕ × ℕ × ℕ | 0 < x ∧ 0 < y ∧ 0 < z ∧ 0 < n ∧ n ^ z < 2001 ∧
n ^ x + n ^ y = n ^ z} = {(1, 1, 2, 2), (2, 2, 3, 2), (3, 3, 4, 2), (4, 4, 5, 2), (5, 5, 6, 2),
(6, 6, 7, 2), (7, 7, 8, 2), (8, 8, 9, 2), (9, 9, 10, 2)} := by

    ext ⟨x, y, z, n⟩
    constructor

    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨hx, hy, hz, hn1, hn2, h⟩

      -- we first show that x = y
      have o: x = y := by
        by_contra! o
        have l: x < y ∨ y < x := by omega
        rcases l with l | l
        -- case 1: x < y
        .
          have eq: n ^ y = n ^ x * n ^ (y - x) := by
            rw [← Nat.pow_add]
            rw [← show y = x + (y - x) by omega]
          rw [eq] at h
          rw [show n ^ x + n ^ x * n ^ (y - x) = n ^ x * (1 + n ^ (y - x)) by ring] at h
          have o: n ^ x ∣ n ^ z := by
            rw [← h]
            simp
          rw [Nat.pow_dvd_pow_iff_le_right] at o
          have eq2: n ^ z = n ^ x * n ^ (z - x) := by
            rw [← Nat.pow_add]
            rw [← show z = x + (z - x) by omega]
          rw [eq2] at h
          rw [Nat.mul_left_cancel_iff] at h
          have i: n ∣ n ^ (z - x) := by
            apply dvd_pow_self
            by_contra! i
            simp [i] at h
            have o: n ≠ 0 := by omega
            simp [o] at h
          rw [← h] at i
          have c: n ∣ 1 := by
            rw [show 1 = 1 + n ^ (y - x) - n ^ (y - x) by omega]
            apply Nat.dvd_sub
            omega
            exact i
            apply dvd_pow_self
            by_contra! c
            replace c: x = y := by omega
            linarith
          apply Nat.le_of_dvd  at c
          replace c: n = 1 := by
            omega
          simp [c] at h
          norm_num
          apply Nat.pos_pow_of_pos
          omega
          by_contra! v
          replace v: n = 1 := by
            omega
          simp [v] at h

        -- case 2: y < x, similar as above
        .
          have eq: n ^ x = n ^ y * n ^ (x - y) := by
            rw [← Nat.pow_add]
            rw [← show x = y + (x - y) by omega]
          rw [eq] at h
          rw [show n ^ y * n ^ (x - y) + n ^ y = n ^ y * (1 + n ^ (x - y)) by ring] at h
          have o: n ^ y ∣ n ^ z := by
            rw [← h]
            simp
          rw [Nat.pow_dvd_pow_iff_le_right] at o
          have eq2: n ^ z = n ^ y * n ^ (z - y) := by
            rw [← Nat.pow_add]
            rw [← show z = y + (z - y) by omega]
          rw [eq2] at h
          rw [Nat.mul_left_cancel_iff] at h
          have i: n ∣ n ^ (z - y) := by
            apply dvd_pow_self
            by_contra! i
            simp [i] at h
            have o: n ≠ 0 := by omega
            simp [o] at h
          rw [← h] at i
          have c: n ∣ 1 := by
            rw [show 1 = 1 + n ^ (x - y) - n ^ (x - y) by omega]
            apply Nat.dvd_sub
            omega
            exact i
            apply dvd_pow_self
            by_contra! c
            replace c: x = y := by omega
            linarith
          apply Nat.le_of_dvd  at c
          replace c: n = 1 := by
            omega
          simp [c] at h
          norm_num
          apply Nat.pos_pow_of_pos
          omega
          by_contra! v
          replace v: n = 1 := by
            omega
          simp [v] at h

      -- now we have x = y
      .
        simp [o] at *
        clear hx o
        rw [show n ^ y + n ^ y = n ^ y * 2 by ring] at h
        have o: n ^ y ∣ n ^ z := by
          rw [← h]
          simp
        rw [Nat.pow_dvd_pow_iff_le_right] at o
        have eq: n ^ z = n ^ y * n ^ (z - y) := by
          rw [← Nat.pow_add]
          rw [← show z = y + (z - y) by omega]
        rw [eq] at h
        rw [Nat.mul_left_cancel_iff] at h
        -- then we must have n ∣ 2
        have i: n ∣ 2 := by
          rw [h]
          apply dvd_pow_self
          by_contra! i
          simp [i] at h
        apply Nat.le_of_dvd at i
        -- then we show that n = 2
        have j: n ≠ 1 := by
          by_contra! j
          simp [j] at h
        replace j: n = 2 := by omega
        simp [j] at *
        clear hn1 i j
        symm at h
        rw [Nat.pow_eq_self_iff] at h
        replace h: z = y + 1 := by omega
        simp [h] at *
        clear hz o eq
        have ly: y < 10 := by
          by_contra! ly
          replace hn2: 2 ^ (y + 1) < 2 ^ 11 := by
            omega
          rw [Nat.pow_lt_pow_iff_right] at hn2
          omega
          norm_num
        omega
        norm_num
        norm_num
        apply Nat.pos_pow_of_pos
        omega
        by_contra! v
        replace v: n = 1 := by
          omega
        simp [v] at h

    -- the backward direction
    .
      intro h
      simp at h
      simp [h]
      rcases h with h | h | h | h | h | h | h | h | h
      all_goals simp [h]

  -- finally, we compute the cardinality
  rw [h_eq]
  simp [Set.encard_insert_of_not_mem]
  norm_num
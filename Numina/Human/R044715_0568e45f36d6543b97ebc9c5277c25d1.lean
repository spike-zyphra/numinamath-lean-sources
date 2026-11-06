import Mathlib

/-Given that 0 < x, y, z ≤ 1, prove the inequality:
x / (2 + x * y + y * z) + y / (2 + y * z + z * x) +
    z / (2 + z * x + x * y) ≤
    (x + y + z) / (x + y + z + x * y * z)
    Under what conditions does equality hold?-/

theorem inequalities_619868 (x y z : ℝ) (lx : 0 < x) (ly : 0 < y) (lz : 0 < z)
    (rx : x ≤ 1) (ry: y ≤ 1) (rz : z ≤ 1) :
    x / (2 + x * y + y * z) + y / (2 + y * z + z * x) +
    z / (2 + z * x + x * y) ≤
    (x + y + z) / (x + y + z + x * y * z) ∧
    (x / (2 + x * y + y * z) + y / (2 + y * z + z * x) +
    z / (2 + z * x + x * y) = (x + y + z) / (x + y + z + x * y * z) ↔ x = 1 ∧ y = 1 ∧ z = 1) := by

  -- we first show the strict inequality when the condition is not held
    have h: ¬ (x = 1 ∧ y = 1 ∧ z = 1) → x / (2 + x * y + y * z) + y / (2 + y * z + z * x) +
    z / (2 + z * x + x * y) < (x + y + z) / (x + y + z + x * y * z) := by
      intro h
      simp at h
      by_cases s: x = 1 ∧ z = 1

      -- case x = z = 1
      .
        simp [s] at h
        rcases s with ⟨s, r⟩
        rw [s,r]
        field_simp
        replace h: y < 1 := by
          by_contra! o
          replace o: y = 1 := by nlinarith
          simp [o] at h
        norm_num
        rw [div_lt_div_iff₀]
        ring_nf
        have o: 0 < 36 + y * 78 + y ^ 2 * 58 + y ^ 3 * 18 + y ^ 4 * 2 -
        (30 + y * 70 + y ^ 2 * 62 + y ^ 3 * 26 + y ^ 4 * 4) := by
          ring_nf
          have o1: 0 < 8 * y - 8 * y ^ 3 := by
            rw [show 8 * y - 8 * y ^ 3 = 8 * (y - y ^ 3) by ring]
            simp
            have oy: y ^ 2 < 1 := by
              nlinarith
            rw [show y ^ 3 = y * y ^ 2 by ring]
            nlinarith
          have o2: 0 < 6 - 4 * y ^ 2 - 2 * y ^ 4 := by
            have s2: y ^ 2 < 1 := by
              nlinarith
            have s3: y ^ 4 < 1 := by
              nlinarith
            nlinarith
          nlinarith [o1, o2]
        nlinarith
        positivity
        positivity

      -- case x < 1 ∨ z < 1
      .
        -- we show the strict inequality
        have lx: x / (2 + x * y + y * z) < x / (x + y + z + x * y * z) := by
          have l: x + y + z + x * y * z < 2 + x * y + y * z := by
            have h1: 0 < (1 / 2 * y - 1) * (x + z - 2) := by
              have s1: 1 / 2 * y - 1 < 0 := by
                field_simp
                linarith
              have s2: x + z - 2 < 0 := by
                have s3: x + z - 2 ≤ 0 := by nlinarith
                by_contra! o
                replace o: x + z = 2 := by nlinarith
                have o1: x = 1 := by nlinarith
                have o2: z = 1 := by nlinarith
                simp [o1, o2] at s
              nlinarith

            -- then we simplify the inequality
            replace h1: x + y + z < 2 + 1 / 2 * y * (x + z) := by nlinarith
            replace h1: x + y + z + y * (1 / 2 * (x + z)) < 2 + y * (x + z) := by nlinarith

            -- then we show xyz ≤ z * (1 / 2 * (x + y)) by AM-GM
            have h2: x * z ≤ 1 / 2 * (x + z) := by
              field_simp
              nlinarith

            -- use h1 and h2 to show the inequality
            nlinarith [h1, h2]

          apply div_lt_div_of_pos_left
          exact lx
          positivity
          exact l

        -- similar foy y, but not strict
        have ly: y / (2 + y * z + z * x) ≤ y / (x + y + z + x * y * z) := by
          have l: x + y + z + x * y * z ≤ 2 + y * z + z * x := by
            have h1: 0 ≤  (1 / 2 * z - 1) * (x + y - 2) := by
              have s1: 1 / 2 * z - 1 < 0 := by
                field_simp
                linarith
              have s2: x + y - 2 ≤ 0 := by
                nlinarith
              nlinarith

            -- then we simplify the inequality
            replace h1: x + y + z ≤ 2 + 1 / 2 * z * (x + y) := by nlinarith
            replace h1: x + y + z + z * (1 / 2 * (x + y)) ≤ 2 + z * (x + y) := by nlinarith

            -- then we show xyz ≤ x * (1 / 2 * (y + z)) by AM-GM
            have h2: x * y ≤ 1 / 2 * (x + y) := by
              field_simp
              nlinarith

            -- use h1 and h2 to show the inequality
            nlinarith [h1, h2]

          rw [div_le_div_iff_of_pos_left]
          exact l
          positivity
          positivity
          positivity

        -- similar for z
        have lz: z / (2 + z * x + x * y) ≤ z / (x + y + z + x * y * z) := by
          have l: x + y + z + x * y * z ≤ 2 + z * x + x * y := by
            have h1: 0 ≤  (1 / 2 * x - 1) * (y + z - 2) := by
              have s1: 1 / 2 * x - 1 < 0 := by
                field_simp
                linarith
              have s2: y + z - 2 ≤ 0 := by
                nlinarith
              nlinarith

            -- then we simplify the inequality
            replace h1: x + y + z ≤ 2 + 1 / 2 * x * (y + z) := by nlinarith
            replace h1: x + y + z + x * (1 / 2 * (y + z)) ≤ 2 + x * (y + z) := by nlinarith

            -- then we show xyz ≤ y * (1 / 2 * (x + z)) by AM-GM
            have h2: y * z ≤ 1 / 2 * (y + z) := by
              field_simp
              nlinarith

            -- use h1 and h2 to show the inequality
            nlinarith [h1, h2]

          rw [div_le_div_iff_of_pos_left]
          exact l
          positivity
          positivity
          positivity

        -- then we combine the inequalities
        have eq: (x + y + z) / (x + y + z + x * y * z)
         = x / (x + y + z + x * y * z) +
          y / (x + y + z + x * y * z) +
          z / (x + y + z + x * y * z) := by
          field_simp
        rw [eq]
        nlinarith


    -- then we can use h to prove the result
    constructor
    -- we show the inequality
    .
      by_cases s: x = 1 ∧ y = 1 ∧ z = 1
      .
        simp [s]
        norm_num
      .
        simp [s] at h
        linarith

    -- we show the equality condition
    .
      constructor
      .
        intro l
        by_contra! s
        replace s: ¬ (x = 1 ∧ y = 1 ∧ z = 1) := by
          by_contra! o
          simp [o] at s
        simp [s] at h
        rw [l] at h
        simp at h
      .
        intro l
        simp [l]
        norm_num
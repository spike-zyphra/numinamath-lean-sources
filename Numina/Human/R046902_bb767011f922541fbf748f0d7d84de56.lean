import Mathlib

open Real

/- Example 4 Let $x, y, z$ be distinct non-negative real numbers. Prove:
$$
\frac{1}{(x-y)^{2}}+\frac{1}{(y-z)^{2}}+\frac{1}{(z-x)^{2}} \geqslant \frac{4}{x y+y z+z x},
$$

and determine the equality conditions.
(2008, Vietnam Mathematical Olympiad) -/

theorem inequalities_99114 (x y z : ℝ) (hz : 0 ≤ z) (hy : z < y) (hx : y < x)
:
    4 / (x * y + y * z + z * x) ≤ 1 / (x - y)^2 + 1 / (y - z)^2 + 1 / (z - x)^2 ∧
    (4 / (x * y + y * z + z * x) = 1 / (x - y)^2 + 1 / (y - z)^2 + 1 / (z - x)^2 ↔
      z = 0 ∧ x * y = (x - y) ^ 2) := by

    constructor

    -- the forward direction
    .
      set m:= x - y
      set n:= y - z
      have lm: 0 < m := by
        simp [m]
        linarith
      have ln: 0 < n := by
        simp [n]
        linarith
      rw [show (z - x) ^ 2 = (m + n) ^ 2 by simp [m, n]; ring]
      -- simplify left side
      have r: x * y + y * z + z * x = 3 * z ^ 2 + (2 * m + 4 * n) * z + n * (m + n) := by
        simp [m, n]
        ring
      rw [r]
      clear r
      -- give upper bound for the left side
      have lr: 4 / (3 * z ^ 2 + (2 * m + 4 * n) * z + n * (m + n)) ≤ 4 / (n * (m + n)) := by
        rw [div_le_div_iff_of_pos_left]
        nlinarith
        norm_num
        nlinarith
        nlinarith
      have l: 4 / (n * (m + n)) ≤ 1 / m ^ 2 + 1 / n ^ 2 + 1 / (m + n) ^ 2 := by
        clear lr
        rw [div_le_iff₀]
        have eq: (1 / m ^ 2 + 1 / n ^ 2 + 1 / (m + n) ^ 2) * (n * (m + n))
          = n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) + 2 := by
          field_simp
          clear_value m n
          ring
        rw [eq]
        clear eq
        have s: 2 ≤ n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) := by    -- use AM-GM
          set a:= n * (m + n) / m ^ 2
          have o: m ^ 2 / (n * (m + n)) = 1 / a := by
            field_simp
            simp [a]
            field_simp
          rw [o]
          have la: 0 < a := by
            simp [a]
            rw [div_pos_iff_of_pos_right]
            nlinarith
            nlinarith
          clear_value a
          clear * - la
          have l: 0 ≤ a + 1 / a - 2 := by
            rw [show a + 1 / a - 2 = (a - 1) ^ 2 / a by field_simp; ring]
            apply div_nonneg
            nlinarith
            linarith
          nlinarith
        nlinarith
        nlinarith

      nlinarith


    -- the backward direction: show the equality condition
    .
      constructor
      .
        intro h
        -- we first show that z = 0
        have lz: z = 0 := by
          by_contra! lz
          -- then we show that the inequality is strict
          have c: 4 / (x * y + y * z + z * x) < 1 / (x - y) ^ 2 + 1 / (y - z) ^ 2 + 1 / (z - x) ^ 2 := by
            clear h
            replace hz: 0 < z := by
              by_contra! hz
              replace hz: z = 0 := by
                linarith
              simp [hz] at lz
            clear lz
            set m:= x - y
            set n:= y - z
            have lm: 0 < m := by
              simp [m]
              linarith
            have ln: 0 < n := by
              simp [n]
              linarith
            rw [show (z - x) ^ 2 = (m + n) ^ 2 by simp [m, n]; ring]
            -- simplify left side
            have r: x * y + y * z + z * x = 3 * z ^ 2 + (2 * m + 4 * n) * z + n * (m + n) := by
              simp [m, n]
              ring
            rw [r]
            clear r
            -- give upper bound for the left side
            have lr: 4 / (3 * z ^ 2 + (2 * m + 4 * n) * z + n * (m + n)) < 4 / (n * (m + n)) := by
              rw [div_lt_div_iff_of_pos_left]
              nlinarith
              norm_num
              nlinarith
              nlinarith
            have l: 4 / (n * (m + n)) ≤ 1 / m ^ 2 + 1 / n ^ 2 + 1 / (m + n) ^ 2 := by
              clear lr
              rw [div_le_iff₀]
              have eq: (1 / m ^ 2 + 1 / n ^ 2 + 1 / (m + n) ^ 2) * (n * (m + n))
                = n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) + 2 := by
                field_simp
                clear_value m n
                ring
              rw [eq]
              clear eq
              have s: 2 ≤ n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) := by    -- use AM-GM
                set a:= n * (m + n) / m ^ 2
                have o: m ^ 2 / (n * (m + n)) = 1 / a := by
                  field_simp
                  simp [a]
                  field_simp
                rw [o]
                have la: 0 < a := by
                  simp [a]
                  rw [div_pos_iff_of_pos_right]
                  nlinarith
                  nlinarith
                clear_value a
                clear * - la
                have l: 0 ≤ a + 1 / a - 2 := by
                  rw [show a + 1 / a - 2 = (a - 1) ^ 2 / a by field_simp; ring]
                  apply div_nonneg
                  nlinarith
                  linarith
                nlinarith
              nlinarith
              nlinarith

            nlinarith

          rw [h] at c
          linarith

        -- now we show that x * y = (x - y) ^ 2
        simp [lz] at *
        set m:= x - y
        set n:= y
        have im: x = m + n := by
          simp [m, n]
        rw [im]
        simp [im] at h
        have hm: 0 < m := by
          simp [m]
          linarith
        clear_value m n
        clear hx im hz lz
        replace h: ((m + n) * n) * ((m ^ 2)⁻¹ + (n ^ 2)⁻¹ + ((m + n) ^ 2)⁻¹) = 4  := by
          field_simp at h
          field_simp
          nlinarith
        have eq: ((m + n) * n) * ((m ^ 2)⁻¹ + (n ^ 2)⁻¹ + ((m + n) ^ 2)⁻¹) = n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) + 2 := by
          field_simp
          ring
        rw [eq] at h
        clear eq
        replace h: n * (m + n) / m ^ 2 + m ^ 2 / (n * (m + n)) = 2 := by
          linarith
        set a:= n * (m + n) / m ^ 2
        have o: m ^ 2 / (n * (m + n)) = 1 / a := by
          field_simp
          simp [a]
          field_simp
        rw [o] at h
        have la: 0 < a := by
          simp [a]
          rw [div_pos_iff_of_pos_right]
          nlinarith
          nlinarith
        have oa: a = 1 := by
          clear_value a
          clear o
          replace h: a + 1 / a - 2 = 0 := by
            field_simp at h
            field_simp
            linarith
          have eq: a + 1 / a - 2 = (a - 1) ^ 2 / a := by
            field_simp
            ring
          rw [eq] at h
          simp at h
          have n: a ≠ 0 := by
            by_contra! n
            simp [n] at la
          simp [n] at h
          linarith
        field_simp [a] at oa
        linarith

      -- finally, we show that the equality is held if the condition is satisfied
      .
        intro h
        rcases h with ⟨lz, h⟩
        simp [lz] at *
        clear hz lz
        rw [← h]
        have nx: x ≠ 0 := by
          by_contra! nx
          simp [nx] at *
          linarith
        have ny: y ≠ 0 := by
          by_contra! ny
          simp [ny] at *
        have eq: (x * y)⁻¹ + (y ^ 2)⁻¹ + (x ^ 2)⁻¹ - 4 / (x * y) = ((x - y) ^ 2 - x * y) / (x * y) ^ 2 := by
          field_simp
          ring
        replace eq: (x * y)⁻¹ + (y ^ 2)⁻¹ + (x ^ 2)⁻¹ - 4 / (x * y) = 0 := by
          rw [eq]
          rw [← h]
          simp
        nlinarith
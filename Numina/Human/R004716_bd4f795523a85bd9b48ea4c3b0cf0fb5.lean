import Mathlib

/- Determine all rational numbers $r$ such that
the equation $r x^{2}+(r+2) x+3 r-2=0$ has roots and only integer roots. -/

theorem algebra_309008: {r: ℚ | ∃ x1 x2: ℤ, 
    r * x1 ^ 2 + (r + 2) * x1 + 3 * r - 2 = 0 ∧
    r * x2 ^ 2 + (r + 2) * x2 + 3 * r - 2 = 0 ∧
    ∀ x : ℝ, r * x ^ 2 + (r + 2) * x + 3 * r - 2 = 0 → x = x1 ∨ x = x2} = {0, -2 / 9, 2 / 3} := by
    ext r
    simp only [Set.mem_setOf_eq]
    constructor
    -- the forward direction
    .
      intro h
      obtain ⟨x1, x2, h1, h2, h⟩ := h
      by_cases lr: r = 0
      -- case r = 0
      .
        simp [lr] at *
      -- case r ≠ 0
      .
        by_contra! hr -- prove by contradiction
        simp at hr
        simp [lr] at hr

        have g: x1 + x2 = -(r + 2) / r ∧ x1 * x2 = (3 * r - 2) / r:= by  -- apply vieta's theorem
          by_cases i: x1 = x2

          -- case 1: multiple roots
          .
            simp [i] at *
            clear h2 i
            set x1:= -(r + 2) / r - x2 with hx1
            -- we then we show that x1 = x2
            have h':= h
            specialize h x1
            have hl: (r: ℝ) * ↑x1 ^ 2 + (↑r + 2) * ↑x1 + 3 * ↑r - 2 = 0 := by
              norm_cast
              norm_cast at h1
              rw [show ↑(x2 ^ 2) = (x2: ℚ) ^ 2 by simp] at h1
              rw [hx1]
              field_simp
              ring_nf
              have eq: -(r ^ 3 * 2) + r ^ 3 * ↑x2 * 2 + r ^ 4 * 3 + r ^ 4 * ↑x2 + r ^ 4 * ↑x2 ^ 2
                     = r ^ 3 * (r * ↑x2 ^ 2 + (r + 2) * ↑x2 + 3 * r - 2) := by ring
              rw [eq]
              rw [h1]
              simp
            simp [hl] at h
            clear hl
            norm_cast at h
            simp [hx1] at h
            constructor
            .
              nlinarith
            .
              clear h hx1
              clear_value x1
              by_cases lx: x2 = 0
              -- case 1: x2 = 0
              .
                simp [lx] at h1
                replace h1: r = 2 / 3 := by nlinarith
                simp [h1] at hr
              -- case 2: x2 ≠ 0
              .
                set x1:= (3 * r - 2) / (r * x2) with hx1
                -- we show that x1 = x2
                specialize h' x1
                have hl: (r: ℝ) * ↑x1 ^ 2 + (↑r + 2) * ↑x1 + 3 * ↑r - 2 = 0 := by
                  norm_cast
                  simp [hx1]
                  field_simp
                  rw [show  r * (3 * r - 2) ^ 2 * (r * ↑x2) + (r + 2) * (3 * r - 2) * (r * ↑x2) ^ 2 + 3 * r * ((r * ↑x2) ^ 2 * (r * ↑x2)) -
                  (r * ↑x2) ^ 2 * (r * ↑x2) * 2
            =  r ^ 2 * ↑x2 * ((3 * r - 2) ^ 2 + (r + 2) * (3 * r - 2) * ↑x2 + 3 * ((r * ↑x2) ^ 2) -
                   x2 * (r * ↑x2) * 2) by ring]
                  have s: (3 * r - 2) ^ 2 + (r + 2) * (3 * r - 2) * ↑x2 + 3 * ((r * ↑x2) ^ 2) -
                   x2 * (r * ↑x2) * 2 = 0 := by
                     rw [show (3 * r - 2) ^ 2 + (r + 2) * (3 * r - 2) * ↑x2 + 3 * ((r * ↑x2) ^ 2) -
                   x2 * (r * ↑x2) * 2 = (3 * r - 2) * (r * ↑x2 ^ 2 + (r + 2) * ↑x2 + 3 * r - 2) by ring]
                     rw [h1]
                     simp
                  rw [s]
                  simp
                simp [hl] at h'
                clear hl
                norm_cast at h'
                simp [hx1] at h'
                field_simp at h'
                field_simp
                nlinarith

          -- case 2: distinct roots
          .
            clear h
            have l: r * ↑x1 ^ 2 + (r + 2) * ↑x1 + 3 * r - 2
            - (r * ↑x2 ^ 2 + (r + 2) * ↑x2 + 3 * r - 2) = 0 := by nlinarith
            rw [show r * ↑x1 ^ 2 + (r + 2) * ↑x1 + 3 * r - 2
            - (r * ↑x2 ^ 2 + (r + 2) * ↑x2 + 3 * r - 2) = (x1 - x2) * (r * (x1 + x2) + r + 2) by ring] at l
            replace i: (x1: ℚ) - x2 ≠ 0 := by
              norm_cast
              by_contra! j
              replace j: x1 = x2 := by linarith
              simp [j] at i
            simp [i] at l
            constructor
            .
              field_simp
              nlinarith
            .
              replace l: x1 = - (r + 2) / r - x2 := by
                field_simp
                nlinarith
              simp [l]
              field_simp
              ring_nf
              nlinarith

        rcases g with ⟨h_sum, h_prod⟩
        have s: (x1: ℚ) * x2 - (x1 + x2) = 4 := by
          rw [h_prod, h_sum]
          field_simp
          ring
        replace s: ((x1: ℚ) - 1) * (x2 - 1) = 5 := by  -- this is the key step
          nlinarith
        norm_cast at s
        have d: 5 ∣ (x1 - 1) * (x2 - 1) := by
          rw [s]
        have hp: Nat.Prime 5 := by decide
        have d5:= Int.Prime.dvd_mul' hp d
        rcases d5 with r | r
        .  -- case 1
          apply exists_eq_mul_right_of_dvd at r
          obtain ⟨k, hk⟩ := r
          simp [hk] at s
          replace s: 5 * (k * (x2 - 1) - 1) = 0 := by linarith
          simp at s
          replace s: k * (x2 - 1) = 1 := by
            linarith
          rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at s
          rcases s with s | s
          .
            rcases s with ⟨s1,s2⟩
            replace s2: x2 = 2 := by omega
            simp [s1] at hk
            replace hk: x1 = 6 := by omega
            simp [hk, s2] at h_sum
            field_simp at h_sum
            ring_nf at h_sum
            have sr: r = -2 / 9 := by
              nlinarith
            simp [sr] at hr
          .
            rcases s with ⟨s1,s2⟩
            replace s2: x2 = 0 := by omega
            rw [s1] at hk
            have o: ↑(5: ℕ) * (-1: ℤ) = -5 := by
              omega
            rw [o] at hk
            replace hk: x1 = -4 := by omega
            simp [hk, s2] at h_sum
            field_simp at h_sum
            ring_nf at h_sum
            have sr: r = 2 / 3 := by
              nlinarith
            simp [sr] at hr
        .
          -- case 2
          apply exists_eq_mul_right_of_dvd at r
          obtain ⟨k, hk⟩ := r
          simp [hk] at s
          replace s: 5 * (k * (x1 - 1) - 1) = 0 := by linarith
          simp at s
          replace s: k * (x1 - 1) = 1 := by
            linarith
          rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at s
          rcases s with s | s
          .
            rcases s with ⟨s1,s2⟩
            replace s2: x1 = 2 := by omega
            simp [s1] at hk
            replace hk: x2 = 6 := by omega
            simp [hk, s2] at h_sum
            field_simp at h_sum
            ring_nf at h_sum
            have sr: r = -2 / 9 := by
              nlinarith
            simp [sr] at hr
          .
            rcases s with ⟨s1,s2⟩
            replace s2: x1 = 0 := by omega
            rw [s1] at hk
            have o: ↑(5: ℕ) * (-1: ℤ) = -5 := by
              omega
            rw [o] at hk
            replace hk: x2 = -4 := by omega
            simp [hk, s2] at h_sum
            field_simp at h_sum
            ring_nf at h_sum
            have sr: r = 2 / 3 := by
              nlinarith
            simp [sr] at hr


    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h
      -- case r = 0
      .
        simp [h]
        use 1
        norm_num
        use 1
        norm_num
        intro x hx
        nlinarith
      -- case r = -2 / 9
      .
        simp [h]
        use 2
        norm_num
        use 6
        norm_num
        intro x hx
        field_simp at hx
        ring_nf at hx
        rw [show -648 + (x * 432 - x ^ 2 * 54) = -54 * (x - 2) * (x - 6) by ring] at hx
        simp at hx
        rcases hx with hx | hx
        .
          left
          linarith
        .
          right
          linarith
      -- case r = 2 / 3
      .
        simp [h]
        use -4
        norm_num
        use 0
        norm_num
        intro x hx
        field_simp at hx
        ring_nf at hx
        rw [show x * 8 + x ^ 2 * 2 = 2 * x * (x + 4) by ring] at hx
        simp at hx
        rcases hx with hx | hx
        .
          right
          linarith
        .
          left
          linarith
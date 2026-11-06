import Mathlib

/-Given the sets
A={(x,y)∣y=ax+2},B={(x,y)∣y=∣x+1∣}, and
A∩B is a singleton set, find the range of the real number a-/

theorem algebra_189222: {a: ℝ | ∃! x: ℝ, a * x + 2 = |x + 1|} = Set.Iic (-1) ∪ Set.Ici 1 := by

  ext a
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    obtain ⟨x, hx, h⟩ := h
    by_contra! l
    simp at l
    rcases l with ⟨l1, l2⟩

    -- we show that there are two solutions
    -- the first one
    have h1:= h (1 / (1 - a))
    simp at h1
    have l3: 0 ≤ (1 - a)⁻¹ + 1 := by
      have o1: 0 ≤ (1 - a)⁻¹ := by
        field_simp
        rw [one_div_nonneg]
        linarith
      nlinarith
    rw [show |(1 - a)⁻¹ + 1| = (1 - a)⁻¹ + 1 by apply abs_of_nonneg; linarith] at h1
    have o: 1 - a ≠ 0 := by
      by_contra! o
      linarith
    field_simp at h1
    ring_nf at h1
    simp at h1
    -- the second one
    have h2:= h (-3 / (1 + a))
    simp at h2
    have o2: 1 + a ≠ 0 := by
      by_contra! o
      linarith
    have l4: -3 / (1 + a) + 1 ≤ 0 := by
      field_simp
      apply div_nonpos_of_nonpos_of_nonneg
      linarith
      linarith
    rw [show |(-3 / (1 + a)) + 1| = - (-3 / (1 + a) + 1) by apply abs_of_nonpos; linarith] at h2
    field_simp at h2
    ring_nf at h2
    simp at h2

    -- then we derive a contradiction by the two solutions
    nlinarith [h1, h2]

  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h

    -- cases a ≤ -1
    .
      use (1 / (1 - a))
      constructor
      .
        simp
        have o: 1 - a ≠ 0 := by
          by_contra! o
          linarith
        have l3: 0 ≤ (1 - a)⁻¹ + 1 := by
          have o1: 0 ≤ (1 - a)⁻¹ := by
            field_simp
            rw [one_div_nonneg]
            linarith
          nlinarith
        rw [show |(1 - a)⁻¹ + 1| = (1 - a)⁻¹ + 1 by apply abs_of_nonneg; linarith]
        field_simp
        ring
      .
        intro y
        simp
        intro hy
        by_cases l: y ≤ -1
        .
          rw [show |y + 1| = - (y + 1) by apply abs_of_nonpos; linarith] at hy
          have o: 1 - a ≠ 0 := by
            by_contra! o
            linarith
          field_simp
          nlinarith
        .
          rw [show |y + 1| = y + 1 by apply abs_of_nonneg; linarith] at hy
          have o: 1 - a ≠ 0 := by
            by_contra! o
            linarith
          field_simp
          nlinarith

    -- cases a ≥ 1
    .
      by_cases l: a ≤ 2
      .
        -- case a ≤ 2
        use (-3 / (1 + a))
        constructor
        .
          simp
          have o: 1 + a ≠ 0 := by
            by_contra! o
            linarith
          rw [show -3 / (1 + a) + 1 = (a - 2) / (1 + a) by field_simp; ring]
          have l1: (a - 2) / (1 + a) ≤ 0 := by
              apply div_nonpos_of_nonpos_of_nonneg
              linarith
              linarith
          rw [show |(a - 2) / (1 + a)| = - ((a - 2) / (1 + a)) by apply abs_of_nonpos; linarith]
          field_simp
          ring
        .
          intro y hy
          by_cases ly: y ≤ -1
          .
            rw [show |y + 1| = - (y + 1) by apply abs_of_nonpos; linarith] at hy
            have o: 1 + a ≠ 0 := by
              by_contra! o
              linarith
            field_simp
            nlinarith
          .
            rw [show |y + 1| = y + 1 by apply abs_of_nonneg; linarith] at hy
            have o: 1 + a ≠ 0 := by
              by_contra! o
              linarith
            simp at ly
            clear o
            have c: y + 1 < a * y + 2 := by
              clear hy
              by_cases r: y ≤ 0
              .
                nlinarith
              .
                nlinarith
            rw [hy] at c
            simp at c

      -- case a > 2
      .
        simp at l
        clear h
        use (1 / ( 1 - a))
        constructor
        .
          simp
          have o: 1 - a ≠ 0 := by
            by_contra! o
            linarith
          have o2: a - 1 ≠ 0 := by
            by_contra! o
            linarith
          rw [show (1 - a)⁻¹ + 1 = (a - 2) / (a - 1) by field_simp; ring]
          have l1: 0 ≤ (a - 2) / (a - 1) := by
              apply div_nonneg
              linarith
              linarith
          rw [show |(a - 2) / (a - 1)| = (a - 2) / (a - 1) by apply abs_of_nonneg; linarith]
          field_simp
          ring
        .
          intro y hy
          by_cases ly: y ≤ -1
          .
            rw [show |y + 1| = - (y + 1) by apply abs_of_nonpos; linarith] at hy
            nlinarith
          .
            rw [show |y + 1| = y + 1 by apply abs_of_nonneg; linarith] at hy
            have o: 1 - a ≠ 0 := by
              by_contra! o
              linarith
            simp at ly
            field_simp
            nlinarith
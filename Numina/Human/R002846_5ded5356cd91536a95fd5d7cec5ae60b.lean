import Mathlib

-- lemma_1 shows that k ^ 2 ≤ 2
lemma lemma_1 (k: ℝ) (hk: 2 < k ^ 2): {(x, y): ℝ × ℝ | x ^ 2 - y ^ 2 = 0
  ∧ (x - k) ^ 2 + y ^ 2 = 1}.encard = 0 := by
  simp
  ext ⟨x, y⟩
  simp
  intro h
  replace h: y ^ 2 = x ^ 2 := by
    linarith
  simp [h]
  by_contra! o
  replace o: (x - k) ^ 2 + x ^ 2 - 1 = 0 := by
    rw [o]
    norm_num
  rw [show  (x - k) ^ 2 + x ^ 2 - 1 = 2 * (x - k / 2) ^ 2 + k ^ 2 / 2 - 1 by ring] at o
  nlinarith

-- lemma_2 tackles the case when k = 1 or k = -1
lemma lemma_2 (k: ℝ) (hk: k = 1 ∨ k = -1): {(x, y): ℝ × ℝ | x ^ 2 - y ^ 2 = 0
  ∧ (x - k) ^ 2 + y ^ 2 = 1}.encard = 3 := by
    rw [Set.encard_eq_three]
    rcases hk with h | h

    -- k = 1
    . use (1, 1)
      use (1, -1)
      use (0, 0)
      constructor
      .
        simp
        by_contra! o
        have s: 1 = ((1: ℝ), (1: ℝ)) := by
          simp
        rw [s] at o
        have f: ((1: ℝ),(1: ℝ)).2 = (1, -1).2 := by
          rw [o]
        simp at f
        norm_num at f
      .
        constructor
        .
          norm_num
        .
          constructor
          .
            norm_num
          .
            ext ⟨x, y⟩
            simp
            constructor
            -- the forward direction
            .
              simp [h]
              intro h1 h2
              replace h2: (x - 1) * x = 0 := by nlinarith
              simp at h2
              rcases h2 with i | i
              .
                replace i: x = 1 := by
                  linarith
                simp [i] at *
                replace h1: (y - 1) * (y + 1) = 0 := by nlinarith
                simp at h1
                rcases h1 with j | j
                .
                  replace j: y = 1 := by
                    linarith
                  simp [j]
                .
                  replace j: y = -1 := by
                    linarith
                  simp [j]
              .
                simp [i] at *
                simp [h1]
            -- the backward direction
            .
              intro l
              rcases l with l | l | l
              all_goals simp [l, h]

    -- k = -1
    .
      use (-1, 1)
      use (-1, -1)
      use (0, 0)
      constructor
      .
        simp
        norm_num
      .
        constructor
        .
          norm_num
        .
          constructor
          .
            norm_num
          .
            ext ⟨x, y⟩
            simp
            constructor
            -- the forward direction
            .
              simp [h]
              intro h1 h2
              replace h2: (x + 1) * x = 0 := by nlinarith
              simp at h2
              rcases h2 with i | i
              .
                replace i: x = -1 := by
                  linarith
                simp [i] at *
                replace h1: (y - 1) * (y + 1) = 0 := by nlinarith
                simp at h1
                rcases h1 with j | j
                .
                  replace j: y = 1 := by
                    linarith
                  simp [j]
                .
                  replace j: y = -1 := by
                    linarith
                  simp [j]
              .
                simp [i] at *
                simp [h1]
            -- the backward direction
            .
              intro l
              rcases l with l | l | l
              all_goals simp [l, h]

-- lemma_3 shows the case when k = √2 or k = -√2
lemma lemma_3 (k: ℝ) (hk: k = √2 ∨ k = -√2): {(x, y): ℝ × ℝ | x ^ 2 - y ^ 2 = 0
  ∧ (x - k) ^ 2 + y ^ 2 = 1}.encard = 2 := by

    rw [Set.encard_eq_two]
    rcases hk with h | h

    -- k = √2
    .
      use (√2 / 2, √2 / 2)
      use (√2 / 2, -√2 / 2)
      constructor
      .
        norm_num
        field_simp
        by_contra! o
        replace o: √2 = 0 := by linarith
        norm_num at o
      .
        ext ⟨x, y⟩
        simp
        constructor
        -- the forward direction
        .
          intro l
          simp [h] at l
          rcases l with ⟨l, r⟩
          replace r: (x - √2) ^ 2 + x ^ 2 - 1 = 0 := by
            linarith
          have eq: (x - √2) ^ 2 + x ^ 2 - 1 = 2 * (x - √2 / 2) ^ 2 := by
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          rw [eq] at r
          clear eq
          simp at r
          replace r: x = √2 / 2 := by
            linarith
          simp [r] at *
          field_simp at l
          have eq: 2 - 2 ^ 2 * y ^ 2 = 4 * (√2 / 2 - y) * (√2 / 2 + y) := by
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          rw [eq] at l
          clear eq
          simp at l
          rcases l with i | i
          .
            replace i: y = √2 / 2 := by
              linarith
            simp [i]
          .
            replace i: y = -√2 / 2 := by
              linarith
            simp [i]
        -- the backward direction
        .
          intro l
          rcases l with l | l
          .
            simp [l, h]
            field_simp
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          .
            simp [l, h]
            field_simp
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring

    -- k = -√2
    .
      use (-√2 / 2, √2 / 2)
      use (-√2 / 2, -√2 / 2)
      constructor
      .
        norm_num
        field_simp
        by_contra! o
        replace o: -√2 = 0 := by linarith
        norm_num at o
      .
        ext ⟨x, y⟩
        simp
        constructor
        -- the forward direction
        .
          intro l
          simp [h] at l
          rcases l with ⟨l, r⟩
          replace r: (x + √2) ^ 2 + x ^ 2 - 1 = 0 := by
            linarith
          have eq: (x + √2) ^ 2 + x ^ 2 - 1 = 2 * (x + √2 / 2) ^ 2 := by
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          rw [eq] at r
          clear eq
          simp at r
          replace r: x = -√2 / 2 := by
            linarith
          simp [r] at *
          field_simp at l
          have eq: 2 - 2 ^ 2 * y ^ 2 = 4 * (√2 / 2 - y) * (√2 / 2 + y) := by
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          rw [eq] at l
          clear eq
          simp at l
          rcases l with i | i
          .
            replace i: y = √2 / 2 := by
              linarith
            simp [i]
          .
            replace i: y = -√2 / 2 := by
              linarith
            simp [i]
        -- the backward direction
        .
          intro l
          rcases l with l | l
          .
            simp [l, h]
            field_simp
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring
          .
            simp [l, h]
            field_simp
            ring_nf
            rw [show √2 ^ 2 = 2 by norm_num]
            ring


/-For which k does the system x^2 - y^2 = 0, (x-k)^2 + y^2 = 1 have exactly (1) two, (2) three real solutions?-/

theorem algebra_121244: {k: ℝ | {(x, y): ℝ × ℝ | x ^ 2 - y ^ 2 = 0
  ∧ (x - k) ^ 2 + y ^ 2 = 1}.encard = 2} = {√2, -√2} ∧
  {k: ℝ | {(x, y): ℝ × ℝ | x ^ 2 - y ^ 2 = 0 ∧ (x - k) ^ 2 + y ^ 2 = 1}.encard = 3} = {1, -1} := by

  constructor

  -- the first part
  .
    ext k
    constructor

    -- the forward direction
    .
      intro h
      rw [Set.mem_setOf_eq] at h
      simp
      by_contra! o

      -- apply lemma, we get that k ^ 2 ≤ 2
      have r: k ^ 2 ≤ 2 := by
        by_contra! r
        apply lemma_1 at r
        rw [r] at h
        norm_num at h
      replace r: k ^ 2 < 2 := by
        by_contra! s
        have v: k ^ 2 = 2 := by
          linarith
        symm at v
        by_cases f: 0 ≤ k
        .
          rw [← Real.sqrt_eq_iff_eq_sq] at v
          simp [← v] at o
          norm_num
          exact f
        .
          simp at f
          rw [show k ^ 2 = (-k) ^ 2 by ring] at v
          set j:= -k
          rw [← Real.sqrt_eq_iff_eq_sq] at v
          simp [j] at v
          replace v: k = -√2 := by
            linarith
          simp [v] at o
          norm_num
          simp [j]
          linarith
      clear o

      -- use lemma_2, we show that k ≠ 1, -1
      have ne: ¬ (k = 1 ∨ k = -1) := by
        by_contra! o
        apply lemma_2 at o
        rw [o] at h
        norm_num at h

      -- we show that the set has at least 3 elements
      set x1:= k / 2 + √(2 - k ^ 2) / 2
      set x2:= k / 2 - √(2 - k ^ 2) / 2
      have f1: (x1 - k) ^ 2 + x1 ^ 2 = 1 := by
        simp [x1]
        ring_nf
        have eq: √(2 - k ^ 2) ^ 2 = 2 - k ^ 2 := by
           symm
           rw [← Real.sqrt_eq_iff_eq_sq]
           ring_nf
           nlinarith
           apply Real.sqrt_nonneg
        rw [eq]
        ring
      have f2: (x2 - k) ^ 2 + x2 ^ 2 = 1 := by
        simp [x2]
        ring_nf
        have eq: √(2 - k ^ 2) ^ 2 = 2 - k ^ 2 := by
           symm
           rw [← Real.sqrt_eq_iff_eq_sq]
           ring_nf
           nlinarith
           apply Real.sqrt_nonneg
        rw [eq]
        ring

      -- we list three different elements
      have t: {(x1, x1), (x1, -x1), (x2, x2)} ⊆ {(x, y) | x ^ 2 - y ^ 2 = 0 ∧ (x - k) ^ 2 + y ^ 2 = 1} := by
        intro ⟨x, y⟩ s
        simp at s
        simp
        rcases s with s | s | s
        .
          rcases s with ⟨p, q⟩
          simp [p, q]
          exact f1
        .
          simp [s]
          exact f1
        .
          simp [s]
          exact f2
      have ct: ({(x1, x1), (x1, -x1), (x2, x2)}: Set (ℝ × ℝ)).encard = 3 := by
        rw [Set.encard_eq_three]
        use (x1, x1)
        use (x1, -x1)
        use (x2, x2)
        constructor
        .
          simp [x1]
          by_contra! o
          field_simp at o
          replace o: √(2 - k ^ 2) = -k := by nlinarith
          rw [Real.sqrt_eq_iff_eq_sq] at o
          ring_nf at o
          replace o: (k - 1) * (k + 1) = 0 := by
            nlinarith
          simp at o
          rcases o with i | i
          .
            replace i: k = 1 := by
              linarith
            simp [i] at ne
          .
            replace i: k = -1 := by
              linarith
            simp [i] at ne
          linarith
          rw [← o]
          apply Real.sqrt_nonneg
        .
          constructor
          .
            simp [x1, x2]
            by_contra! o
            field_simp at o
            replace o: √(2 - k ^ 2) = 0 := by linarith
            rw [Real.sqrt_eq_iff_eq_sq] at o
            nlinarith
            linarith
            norm_num
          .
            constructor
            .
              simp
              intro g
              by_contra! p
              simp [x1, x2] at g
              replace g: √(2 - k ^ 2) = 0 := by
                linarith
              rw [Real.sqrt_eq_iff_eq_sq] at g
              nlinarith
              linarith
              norm_num
            .
              simp

      apply Set.Finite.eq_of_subset_of_encard_le' at t
      simp [ct, h] at t
      norm_num at t
      rw [t] at ct
      simp at h
      rw [h] at ct
      norm_num at ct
      simp

    -- the backward direction
    .
      intro h
      simp at h
      rw [Set.mem_setOf_eq]
      apply lemma_3
      exact h


  -- the second part
  .
    ext k
    constructor

    -- the forward direction
    .
      intro h
      rw [Set.mem_setOf_eq] at h
      simp
      by_contra! o

      -- apply lemma, we get that k ^ 2 ≤ 2
      have r: k ^ 2 ≤ 2 := by
        by_contra! r
        apply lemma_1 at r
        rw [r] at h
        norm_num at h
      replace r: k ^ 2 < 2 := by
        by_contra! s
        have v: k ^ 2 = 2 := by
          linarith
        symm at v
        by_cases f: 0 ≤ k
        .
          rw [← Real.sqrt_eq_iff_eq_sq] at v
          symm at v
          have i:= lemma_3 k
          simp [v] at i h
          rw [h] at i
          norm_num at i
          norm_num
          exact f
        .
          simp at f
          rw [show k ^ 2 = (-k) ^ 2 by ring] at v
          set j:= -k
          rw [← Real.sqrt_eq_iff_eq_sq] at v
          simp [j] at v
          replace v: k = -√2 := by
            linarith
          have i:= lemma_3 k
          simp [v] at i h
          rw [h] at i
          norm_num at i
          norm_num
          simp [j]
          linarith

      set x1:= k / 2 + √(2 - k ^ 2) / 2
      set x2:= k / 2 - √(2 - k ^ 2) / 2
      have f1: (x1 - k) ^ 2 + x1 ^ 2 = 1 := by
        simp [x1]
        ring_nf
        have eq: √(2 - k ^ 2) ^ 2 = 2 - k ^ 2 := by
           symm
           rw [← Real.sqrt_eq_iff_eq_sq]
           ring_nf
           nlinarith
           apply Real.sqrt_nonneg
        rw [eq]
        ring
      have f2: (x2 - k) ^ 2 + x2 ^ 2 = 1 := by
        simp [x2]
        ring_nf
        have eq: √(2 - k ^ 2) ^ 2 = 2 - k ^ 2 := by
           symm
           rw [← Real.sqrt_eq_iff_eq_sq]
           ring_nf
           nlinarith
           apply Real.sqrt_nonneg
        rw [eq]
        ring

      -- we list four different elements
      have t: {(x1, x1), (x1, -x1), (x2, x2), (x2, -x2)} ⊆ {(x, y) | x ^ 2 - y ^ 2 = 0 ∧ (x - k) ^ 2 + y ^ 2 = 1} := by
        intro ⟨x, y⟩ s
        simp at s
        simp
        rcases s with s | s | s | s
        .
          rcases s with ⟨p, q⟩
          simp [p, q]
          exact f1
        .
          simp [s]
          exact f1
        .
          simp [s]
          exact f2
        .
          simp [s]
          exact f2

      have ct: ({(x1, x1), (x1, -x1), (x2, x2), (x2, -x2)}: Set (ℝ × ℝ)).encard = 4 := by
        have b: ¬ k ^ 2 = 1 := by
          by_contra! b
          replace b: (k - 1) * (k + 1) = 0 := by
            nlinarith
          simp at b
          rcases b with i | i
          .
            replace i: k = 1 := by
              linarith
            simp [i] at o
          .
            replace i: k = -1 := by
              linarith
            simp [i] at o
        have g1: ¬ x1 = x2 := by
          by_contra! u
          simp [x1, x2] at u
          replace u: √(2 - k ^ 2) = 0 := by
            linarith
          rw [Real.sqrt_eq_iff_eq_sq] at u
          replace u: k ^ 2 = 1 := by linarith
          simp [u] at b
          linarith
          norm_num
        have g2: ¬ x2 = -x2 := by
          by_contra! u
          simp [x2] at u
          replace u: √(2 - k ^ 2) = k := by
            linarith
          rw [Real.sqrt_eq_iff_eq_sq] at u
          replace u: k ^ 2 = 1 := by linarith
          simp [u] at b
          linarith
          rw [← u]
          apply Real.sqrt_nonneg
        have g3: ¬ x1 = -x1 := by
          by_contra! u
          simp [x1] at u
          replace u: √(2 - k ^ 2) = -k := by
            linarith
          set j:= -k
          rw [show k ^ 2 = j ^ 2 by ring] at u
          rw [Real.sqrt_eq_iff_eq_sq] at u
          replace u: j ^ 2 = 1 := by linarith
          rw [show j ^ 2 = k ^ 2 by ring] at u
          simp [u] at b
          rw [show j ^ 2 = k ^ 2 by ring]
          linarith
          rw [← u]
          apply Real.sqrt_nonneg
        repeat rw [Set.encard_insert_of_not_mem]
        norm_num
        .
          simp
          exact g2
        .
          simp
          constructor
          .
            intro u
            simp [u] at g1
          .
            exact g1
        .
          simp
          simp [g1, g2, g3]

      apply Set.Finite.eq_of_subset_of_encard_le' at t
      simp [ct, h] at t
      norm_num at t
      rw [t] at ct
      simp at h
      rw [h] at ct
      norm_num at ct
      rw [show (4: ℕ∞) = ↑(4: ℕ) by simp] at ct
      apply Set.finite_of_encard_eq_coe at ct
      exact ct

    -- the backward direction
    .
      intro h
      simp at h
      rw [Set.mem_setOf_eq]
      apply lemma_2
      exact h
      


import Mathlib

/-Find the values of a such that the roots of the equation
x^2−ax+9a=0 are integers.
(Recommended by the Soviet Ministry of Education, 1990-/

theorem algebra_214273: {a: ℝ | ∃ x1 x2: ℤ, x1 ^ 2 - a * x1 + 9 * a = 0 ∧ x2 ^ 2 - a * x2 + 9 * a = 0
  ∧ ∀ y: ℝ, y ^ 2 - a * y + 9 * a = 0 → y = x1 ∨ y = x2}
    = {100, -64, 48, -12, 36, 0} := by

    ext a
    simp only [Set.mem_setOf_eq]
    constructor

    -- the forward direction
    .
      intro h
      simp
      obtain ⟨x1, x2, h1, h2, h⟩ := h
      by_cases l: x2 = x1

      --case 1: x2 = x1, the equation has multiple roots
      .
        clear h2
        set y:= a - x1

        -- we show that y is a root of the equation to get the value of a
        have hy: y ^ 2 - a * y + 9 * a = 0 := by
          simp [y]
          nlinarith
        specialize h y
        simp [hy] at h
        simp [l] at *
        simp [y] at h
        replace h: 2 * x1 = a := by linarith
        replace h: x1 = a / 2 := by linarith
        simp [h] at h1
        ring_nf at h1
        rw [show a * 9 + a ^ 2 * (-1 / 4) = a * (9 - a / 4) by ring] at h1
        simp at h1
        rcases h1 with h1 | h1
        .
          simp [h1]
        .
          replace h1: a = 36 := by nlinarith
          simp [h1]

      -- case 2: x2 ≠ x1, the equation has distinct roots
      .
        clear h

        -- then we show the vieta's lemma
        have u: x1 + x2 = a := by
          have o: (x1 - x2) * (x1 + x2 - a) = 0 := by
            nlinarith
          simp at o
          have s: ¬ x1 - x2 = 0 := by omega
          rify at s
          simp [s] at o
          clear s
          linarith
        have v: x1 * x2 = 9 * a := by
          have o: (x1 + x2) ^ 2 - 2 * (x1 * x2) - a * (x1 + x2) + 18 * a = 0 := by
            nlinarith
          rify at u
          simp [u] at o
          nlinarith

        -- then we can use these to get a
        have w: x1 * x2 = 9 * (x1 + x2) := by
          rify
          nlinarith
        clear v h1 h2 l

        -- we perform a key factorization
        replace w: (x1 - 9) * (x2 - 9) = 81 := by nlinarith
        set p:= x1 - 9
        set q:= x2 - 9
        replace u: a = p + q + 18 := by
          simp [p, q]
          nlinarith
        clear_value p q
        have d: p.natAbs ∈ Nat.divisors 81 := by
          simp
          zify
          replace w: |p * q| = 81 := by
            rw [w]
            rfl
          rw [abs_mul] at w
          rw [← w]
          simp
        have eq: Nat.divisors 81 = {1, 3, 9, 27, 81} := by
          native_decide
        rw [eq] at d
        clear eq
        simp at d
        zify at d
        by_cases l: 0 ≤ p
        .
          -- 0 ≤ p
          rw [show |p| = p by apply abs_of_nonneg; linarith] at d
          rcases d with d | d | d | d | d
          .
            simp [d] at w u
            simp [w] at u
            norm_num at u
            simp [u]
          .
            simp [d] at w u
            replace w: q = 27 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            simp [d] at w u
            replace w: q = 9 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            simp [d] at w u
            replace w: q = 3 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            simp [d] at w u
            replace w: q = 1 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
        .
          -- p < 0
          simp at l
          rw [show |p| = -p by apply abs_of_neg; linarith] at d
          rcases d with d | d | d | d | d
          .
            replace d: p = -1 := by omega
            simp [d] at w u
            replace w: q = -81 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            replace d: p = -3 := by omega
            simp [d] at w u
            replace w: q = -27 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            replace d: p = -9 := by omega
            simp [d] at w u
            replace w: q = -9 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            replace d: p = -27 := by omega
            simp [d] at w u
            replace w: q = -3 := by omega
            simp [w] at u
            norm_num at u
            simp [u]
          .
            replace d: p = -81 := by omega
            simp [d] at w u
            replace w: q = -1 := by omega
            simp [w] at u
            norm_num at u
            simp [u]


    -- the backward direction, check all values of a
    .
      intro h
      simp at h
      rcases h with h | h | h | h | h | h
      all_goals rw [h]; clear h

      -- a = 100
      .
        use 10
        norm_num
        use 90
        norm_num
        intro y h
        rw [show y ^ 2 - 100 * y + 900 = (y - 10) * (y - 90) by ring] at h
        simp at h
        rcases h with h | h
        .
          left
          linarith
        .
          right
          linarith

      -- a = -64
      .
        use -72
        norm_num
        use 8
        norm_num
        intro y h
        rw [show y ^ 2 + 64 * y + -576 = (y + 72) * (y - 8) by ring] at h
        simp at h
        rcases h with h | h
        .
          left
          linarith
        .
          right
          linarith

      -- a = 48
      .
        use 12
        norm_num
        use 36
        norm_num
        intro y h
        rw [show y ^ 2 - 48 * y + 432 = (y - 12) * (y - 36) by ring] at h
        simp at h
        rcases h with h | h
        .
          left
          linarith
        .
          right
          linarith

      -- a = -12
      .
        use -18
        norm_num
        use 6
        norm_num
        intro y h
        rw [show y ^ 2 + 12 * y + -108 = (y + 18) * (y - 6) by ring] at h
        simp at h
        rcases h with h | h
        .
          left
          linarith
        .
          right
          linarith

      -- a = 36
      .
        use 18
        norm_num
        use 18
        norm_num
        intro y h
        rw [show y ^ 2 - 36 * y + 324 = (y - 18) * (y - 18) by ring] at h
        simp at h
        linarith

      -- a = 0
      .
        norm_num
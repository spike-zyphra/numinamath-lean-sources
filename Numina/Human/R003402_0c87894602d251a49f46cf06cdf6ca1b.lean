import Mathlib

/- Se considera la inecuación

$$
|x-1| < a x
$$

donde $a$ es un parámetro real.

a) Discutir la inecuación según los valores de $a$.

b) Caracterizar los valores de $a$ para los cuales la inecuación tiene exactamente DOS soluciones enteras. -/

theorem inequalities_176553 (a : ℝ) :
  {x : ℤ | abs (x - 1) < a * x}.encard = 2 ↔
  1 / 2 < a ∧ a ≤ 2 / 3 := by

  constructor

  -- the forward direction
  .
    intro h
    rw [Set.encard_eq_two] at h
    obtain ⟨x1, x2, ne, h⟩ := h
    by_contra! l
    have f1: x1 ∈ {x: ℤ | ↑|x - 1| < a * ↑x} := by
      rw [h]
      simp
    have f2: x2 ∈ {x: ℤ | ↑|x - 1| < a * ↑x} := by
      rw [h]
      simp
    simp at f1 f2
    by_cases r: a < 0

    -- case a < 0
    .
      clear l
      have l1: x1 < 0 := by
        by_contra! o
        replace f1: 0 < a * x1 := by
          suffices 0 ≤ |↑x1 - (1: ℝ)| by
            linarith
          apply abs_nonneg
        clear *- r f1 o
        rify at o
        nlinarith
      have l2: x2 < 0 := by
        by_contra! o
        replace f2: 0 < a * x2 := by
          suffices 0 ≤ |↑x2 - (1: ℝ)| by
            linarith
          apply abs_nonneg
        clear *- r f2 o
        rify at o
        nlinarith
      rw [show |x1 - (1: ℝ)| = -(x1 - 1) by apply abs_of_neg; rify at l1; nlinarith] at f1
      rw [show |x2 - (1: ℝ)| = -(x2 - 1) by apply abs_of_neg; rify at l2; nlinarith] at f2
      have ra: a < -1 := by
        clear *- l1 f1
        rify at l1
        nlinarith
      -- then we show that 2x1 and 2x2 are in the set
      have g1: 2 * x1 ∈ {x: ℤ | ↑|x - 1| < a * ↑x} := by
        simp
        rw [show |2 * x1 - (1: ℝ)| = -(2 * x1 - 1) by apply abs_of_neg; rify at l1; nlinarith]
        nlinarith
      have g2: 2 * x2 ∈ {x: ℤ | ↑|x - 1| < a * ↑x} := by
        simp
        rw [show |2 * x2 - (1: ℝ)| = -(2 * x2 - 1) by apply abs_of_neg; rify at l2; nlinarith]
        nlinarith
      rw [h] at g1 g2
      simp at g1 g2
      have i1: 2 * x1 ≠ x1 := by
        by_contra! u
        linarith
      have i2: 2 * x2 ≠ x2 := by
        by_contra! u
        linarith
      simp [i1, i2] at g1 g2
      simp [← g1] at g2
      clear *- g2 l1
      nlinarith

    -- case 0 ≤ a
    .
      simp at r
      by_cases j: a = 0

      -- case a = 0
      .
        simp [j] at f1
        absurd f1
        simp

      -- case 0 < a
      .
        replace r: 0 < a := by
          by_contra! i
          have p: a = 0 := by linarith
          simp [p] at j
        clear j
        by_cases i: a ≤ 1 / 2

        -- case a ≤ 1 / 2
        .
          clear l

          -- we show that x1 and x2 must be 1
          have l1: 1 ≤ x1 := by
            by_contra! j
            rw [show |x1 - (1: ℝ)| = -(x1 - 1) by apply abs_of_neg; rify at j; nlinarith] at f1
            have u: 0 ≤ x1 := by
              rify
              nlinarith
            suffices x1 ≠ 0 by omega
            by_contra! y
            simp [y] at f1
            norm_num at f1
          have s1: x1 = 1 := by
            suffices x1 < 2 by omega
            by_contra! l
            rify at l
            rw [show |x1 - (1: ℝ)| = (x1 - 1) by apply abs_of_nonneg; rify at l1; nlinarith] at f1
            clear *- i l f1 l1 r
            nlinarith

          clear l1 f1
          -- similar for x2
          have l2: 1 ≤ x2 := by
            by_contra! j
            rw [show |x2 - (1: ℝ)| = -(x2 - 1) by apply abs_of_neg; rify at j; nlinarith] at f2
            have u: 0 ≤ x2 := by
              rify
              nlinarith
            suffices x2 ≠ 0 by omega
            by_contra! y
            simp [y] at f2
            norm_num at f2
          have s2: x2 = 1 := by
            suffices x2 < 2 by omega
            by_contra! l
            rify at l
            rw [show |x2 - (1: ℝ)| = (x2 - 1) by apply abs_of_nonneg; rify at l2; nlinarith] at f2
            clear *- i l f2 l2 r
            nlinarith
          simp [s1, s2] at ne

        -- finally, for the case 2 / 3 < a
        .
          simp at i
          simp [i] at l
          clear i r

          -- we show that 1 2 3 are in the set
          have z: {1, 2, 3} ⊆ {x: ℤ | ↑|x - 1| < a * ↑x} := by
            intro x hx
            simp at hx
            rcases hx with i | i | i
            .
              simp [i]
              linarith
            .
              simp [i]
              norm_num
              linarith
            .
              simp [i]
              norm_num
              linarith

          rw [h] at z
          clear *- z ne
          have u1: (1: ℤ) ∈ ({x1, x2}: Set ℤ) := by
            apply Set.mem_of_mem_of_subset (by decide) z
          have u2: (2: ℤ) ∈ ({x1, x2}: Set ℤ) := by
            apply Set.mem_of_mem_of_subset (by decide) z
          have u3: (3: ℤ) ∈ ({x1, x2}: Set ℤ) := by
            apply Set.mem_of_mem_of_subset (by decide) z
          simp at u1 u2 u3
          rcases u1 with f | f
          <;> rcases u2 with g | g
          <;> rcases u3 with t | t
          <;> linarith


  -- the backward direction
  .
    intro h
    rcases h with ⟨l, r⟩
    rw [Set.encard_eq_two]
    use 1, 2
    norm_num
    ext x
    constructor
    .
      intro h
      simp at h
      simp
      have p: 0 < x := by
        suffices 0 < a * x by
          rify
          nlinarith
        suffices 0 ≤ |x - (1: ℝ)| by linarith
        apply abs_nonneg
      suffices x < 3 by omega
      by_contra! i
      rify at i
      rw [show |x - (1: ℝ)| = (x - 1) by apply abs_of_nonneg; nlinarith] at h
      nlinarith
    .
      intro h
      simp at h
      rcases h with h | h
      .
        simp [h]
        linarith
      .
        simp [h]
        norm_num
        linarith
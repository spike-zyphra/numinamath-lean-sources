import Mathlib

open Real Set
open scoped BigOperators

/- Given the function $f(x)=-x^{2}+x+m+2$.
If the solution set of the inequality $f(x) ≥ |x|$ contains exactly 1 integer,
then the range of the real number $m$ is . -/

theorem algebra_169171: {m: ℝ | ∃! x: ℤ, -x^2 + x + m + 2 ≥ |x|} = Ico (-2) (-1) := by

  ext m
  constructor

  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    simp
    obtain ⟨x, h1, h2⟩ := h

    -- we show m < 1
    have g1: m < -1 := by
      by_contra! g
      -- then we show that there are 2 solutions, 0 and 1
      have u0:= h2 0
      have u1:= h2 1
      simp at u0 u1
      have v0: 0 ≤ m + 2 := by linarith
      have v1: 1 ≤ m + 2 := by linarith
      simp [v0, v1] at u0 u1
      linarith

    -- then we show m ≥ -2
    have g2: -2 ≤ m := by
      by_contra! g
      -- then we show that there are no solutions
      clear h2 g1
      by_cases hx: 0 ≤ x
      -- case 1: x ≥ 0
      .
        rw [show |x| = x by apply abs_of_nonneg; linarith] at h1
        simp at h1
        nlinarith
      -- case 2: x < 0
      .
        simp at hx
        rw [show |x| = -x by apply abs_of_neg; linarith] at h1
        simp at h1
        replace h1: x ^ 2 - 2 * x ≤ (0: ℝ) := by nlinarith
        rw [show x ^ 2 - 2 * x = x * (x - (2: ℝ)) by ring] at h1
        absurd h1
        simp
        apply mul_pos_of_neg_of_neg
        simp
        omega
        rify at hx
        linarith
    constructor
    .
      exact g2
    .
      exact g1


  -- the backward direction
  .
    intro h
    simp at h
    simp
    -- we show that 0 is the only solution
    use 0
    rcases h with ⟨l, r⟩
    constructor
    .
      simp
      linarith
    .
      simp
      intro y hy
      by_contra! ny
      by_cases ly: 0 ≤ y
      -- case 1: y ≥ 0
      .
        replace ly: 0 < y := by
          by_contra! g
          have f: y = 0 := by linarith
          simp [f] at ny
        clear ny
        rw [show |↑y| = (y: ℝ) by apply abs_of_nonneg; simp; linarith] at hy
        absurd hy
        simp
        by_cases uy: 2 ≤ y
        -- case 1.1: y ≥ 2
        .
          rify at uy
          nlinarith
        -- case 1.2: y < 2
        .
          have o: y = 1 := by omega
          simp [o]
          linarith
      -- case 2: y < 0
      .
        simp at ly
        rw [show |↑y| = -(y: ℝ) by apply abs_of_neg; simp; linarith] at hy
        absurd hy
        simp
        have o: m + 2 < ↑y ^ 2 - 2 * ↑y := by
          have o1: m + 2 < 1 := by linarith
          have o2: 1 ≤ y ^ 2 - 2 * y := by
            have f1: 0 < y ^ 2 - 2 * y := by
              rw [show y ^ 2 - 2 * y = y * (y - 2) by ring]
              apply Int.mul_pos_of_neg_of_neg
              omega
              omega
            omega
          rify at o2
          nlinarith
        nlinarith

import Mathlib

open Real Set
open scoped BigOperators

/- (12) The line $y=b$ intersects the graph of the function $y=|x^2-4x+3|$ at least at three points,
then the range of the real number $b$ is -/

theorem algebra_130130 (f : ℝ → ℝ) (hf : f = λ x => abs (x^2 - 4 * x + 3)) (b : ℝ)
  (h : ∃ x1 x2 x3 : ℝ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧ f x1 = b ∧ f x2 = b ∧ f x3 = b) :
  0 < b ∧ b ≤ 1 := by

  obtain ⟨x1, x2, x3, n1, n2, n3, h1, h2, h3⟩ := h
  by_contra! l
  replace l: 1 < b ∨ b ≤ 0 := by
    by_cases s: b ≤ 0
    .
      right
      exact s
    .
      simp at s
      simp [s] at l
      left
      exact l

  rcases l with l | l

  -- case 1 < b, we show there are only two intersection points
  .
    -- we show that 0 ≤ x1 ^ 2 - 4 * x1 + 3
    have s1: 0 ≤ x1 ^ 2 - 4 * x1 + 3 := by
      by_contra! r
      simp [hf] at h1
      rw [show |x1 ^ 2 - 4 * x1 + 3| = -(x1 ^ 2 - 4 * x1 + 3) by apply abs_of_nonpos; linarith] at h1
      have e: -1 ≤ x1 ^ 2 - 4 * x1 + 3 := by
        have o: 0 ≤ x1 ^ 2 - 4 * x1 + 4 := by
          rw [show x1 ^ 2 - 4 * x1 + 4 = (x1 - 2) ^ 2 by ring]
          nlinarith
        linarith
      nlinarith

    -- we show that 0 ≤ x2 ^ 2 - 4 * x2 + 3
    have s2: 0 ≤ x2 ^ 2 - 4 * x2 + 3 := by
      by_contra! r
      simp [hf] at h2
      rw [show |x2 ^ 2 - 4 * x2 + 3| = -(x2 ^ 2 - 4 * x2 + 3) by apply abs_of_nonpos; linarith] at h2
      have e: -1 ≤ x2 ^ 2 - 4 * x2 + 3 := by
        have o: 0 ≤ x2 ^ 2 - 4 * x2 + 4 := by
          rw [show x2 ^ 2 - 4 * x2 + 4 = (x2 - 2) ^ 2 by ring]
          nlinarith
        linarith
      nlinarith

    -- we show that 0 ≤ x3 ^ 2 - 4 * x3 + 3
    have s3: 0 ≤ x3 ^ 2 - 4 * x3 + 3 := by
      by_contra! r
      simp [hf] at h3
      rw [show |x3 ^ 2 - 4 * x3 + 3| = -(x3 ^ 2 - 4 * x3 + 3) by apply abs_of_nonpos; linarith] at h3
      have e: -1 ≤ x3 ^ 2 - 4 * x3 + 3 := by
        have o: 0 ≤ x3 ^ 2 - 4 * x3 + 4 := by
          rw [show x3 ^ 2 - 4 * x3 + 4 = (x3 - 2) ^ 2 by ring]
          nlinarith
        linarith
      nlinarith

    -- then we can take out the abs sign
    simp [hf] at h1 h2 h3
    rw [show |x1 ^ 2 - 4 * x1 + 3| = x1 ^ 2 - 4 * x1 + 3 by apply abs_of_nonneg; linarith] at h1
    rw [show |x2 ^ 2 - 4 * x2 + 3| = x2 ^ 2 - 4 * x2 + 3 by apply abs_of_nonneg; linarith] at h2
    rw [show |x3 ^ 2 - 4 * x3 + 3| = x3 ^ 2 - 4 * x3 + 3 by apply abs_of_nonneg; linarith] at h3

    -- then we use vieta lemma
    have u1: x1 + x2 = 4 := by
      have o: (x1 - x2) * (x1 + x2 - 4) = 0 := by nlinarith
      simp at o
      rcases o with o | o
      .
        replace o: x1 = x2 := by
          linarith
        simp [o] at n1
      .
        linarith
    have u2: x2 + x3 = 4 := by
      have o: (x2 - x3) * (x2 + x3 - 4) = 0 := by nlinarith
      simp at o
      rcases o with o | o
      .
        replace o: x2 = x3 := by
          linarith
        simp [o] at n2
      .
        linarith

    -- then x1 = x3, which is a contradiction
    have c: x1 = x3 := by linarith
    simp [c] at n3

  -- case b < 0 , we show there are at least three intersection points
  .
    by_cases s: b < 0
    .
      clear l h2 h3 n2 n3
      simp [hf] at h1
      have o: 0 ≤ b := by
        rw [← h1]
        apply abs_nonneg
      linarith
    .
      -- for b = 0, we show there are only two intersection points
      have s: b = 0 := by
        simp at s
        linarith
      clear l
      simp [s] at *
      simp [hf] at h1 h2 h3
      rw [show x1 ^ 2 - 4 * x1 + 3 = (x1 - 1) * (x1 - 3) by ring] at h1
      simp at h1
      rw [show x2 ^ 2 - 4 * x2 + 3 = (x2 - 1) * (x2 - 3) by ring] at h2
      simp at h2
      rw [show x3 ^ 2 - 4 * x3 + 3 = (x3 - 1) * (x3 - 3) by ring] at h3
      simp at h3
      rcases h1 with h1 | h1
      -- case x1 = 1
      .
        replace h1: x1 = 1 := by
          linarith
        simp [h1] at *
        rcases h2 with h2 | h2
        .
          replace h2: x2 = 1 := by
            linarith
          simp [h2] at *
        .
          replace h2: x2 = 3 := by
            linarith
          simp [h2] at *
          rcases h3 with h3 | h3
          .
            replace h3: x3 = 1 := by
              linarith
            simp [h3] at *
          .
            replace h3: x3 = 3 := by
              linarith
            simp [h3] at *
      -- case x1 = 3
      .
        replace h1: x1 = 3 := by
          linarith
        simp [h1] at *
        rcases h2 with h2 | h2
        .
          replace h2: x2 = 1 := by
            linarith
          simp [h2] at *
          rcases h3 with h3 | h3
          .
            replace h3: x3 = 1 := by
              linarith
            simp [h3] at *
          .
            replace h3: x3 = 3 := by
              linarith
            simp [h3] at *
        .
          replace h2: x2 = 3 := by
            linarith
          simp [h2] at *
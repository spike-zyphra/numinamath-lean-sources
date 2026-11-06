import Mathlib

/- Find all pairs of integers $(x,y)$ satisfying the following equality $8x^2y^2 + x^2 + y^2 = 10xy$ -/

theorem number_theory_70844: {(x, y): ℤ × ℤ | 8 * x ^ 2 * y ^ 2 + x ^ 2 + y ^ 2 = 10 * x * y} =
  {(0, 0), (1, 1), (-1, -1)} := by

  ext ⟨x, y⟩
  constructor

  -- the forward direction
  .
    intro h
    simp at h
    simp
    have u: 0 ≤ x * y := by
      nlinarith

    -- we show that |xy| ≤ 1
    have l: |x * y| < 2 := by
      replace h: 8 * (x ^ 2 * y ^ 2) ≤ 10 * x * y := by
        rw [← h]
        nlinarith
      have eq1: x ^ 2 * y ^ 2 = |x * y| ^ 2 := by
        rw [show x ^ 2 * y ^ 2 = (x * y) ^ 2 by ring]
        symm
        rw [show |x * y| = x * y by apply abs_of_nonneg u]
      rw [eq1] at h
      clear eq1
      have eq2: 10 * x * y = 10 * |x * y| := by
        rw [show |x * y| = x * y by apply abs_of_nonneg u]
        ring
      rw [eq2] at h
      clear eq2
      set p:= |x * y|
      have lp: 0 ≤ p := by
        apply abs_nonneg
      nlinarith

    -- then xy = 1 ∨ 0
    rw [show |x * y| = x * y by apply abs_of_nonneg u] at l
    replace l: x * y = 1 ∨ x * y = 0 := by
      omega
    rcases l with l | l
    .
      apply Int.eq_one_or_neg_one_of_mul_eq_one' at l
      omega
    .
      simp at l
      rcases l with l | l
      .
        simp [l] at h
        simp [l, h]
      .
        simp [l] at h
        simp [l, h]


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h
    all_goals simp [h]
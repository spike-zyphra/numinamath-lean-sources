import Mathlib

open BigOperators Real Set

theorem algebra_181457 (a : ℝ) :
  (∃ x : ℝ, sin x ^ 2 + a * cos x - 2 * a = 0) ↔
  0 ≤ a ∧ a ≤ 4 - 2 * sqrt 3 := by
  constructor
  · -- Assume there exists x such that $\sin^2 x + a \cos x - 2a = 0$, prove $0 \leq a \land a \leq 4 - 2\sqrt{3}$.
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by linarith
    rw [h2] at hx
    have h3 : cos x ^ 2 - a * cos x - 1 + 2 * a = 0 := by linarith
    have h4 : cos x ^ 2 - a * cos x + (2 * a - 1) = 0 := by linarith
    have h5 : cos x ≤ 1 := by
      apply Real.cos_le_one
    have h6 : cos x ≥ -1 := by
      apply Real.neg_one_le_cos
    constructor
    · -- Show that 0 ≤ a
      nlinarith [sq_nonneg (cos x - (1 : ℝ)), sq_nonneg (cos x - (2 : ℝ)), h5, h6]
    · -- Show that a ≤ 4 - 2 * Real.sqrt 3
      nlinarith [sq_nonneg (cos x - (a / 2)), sq_nonneg (cos x - (2 - Real.sqrt 3)), sq_nonneg (a - (4 - 2 * Real.sqrt 3)), Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1)]
  · -- Assume $0 \leq a \land a \leq 4 - 2\sqrt{3}$, prove $\exists x, \sin x ^ 2 + a \cos x - 2a = 0$.
    rintro ⟨ha1, ha2⟩
    have h7 : a ^ 2 - 8 * a + 4 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (a - (4 - 2 * Real.sqrt 3)), sq_nonneg (a - (4 + 2 * Real.sqrt 3)), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
    have h19 : ∃ y : ℝ, -1 ≤ y ∧ y ≤ 1 ∧ y ^ 2 - a * y + (2 * a - 1) = 0 := by
      use (a - Real.sqrt (a ^ 2 - 8 * a + 4)) / 2
      constructor
      · nlinarith [Real.sqrt_nonneg (a ^ 2 - 8 * a + 4), Real.sq_sqrt (show (a ^ 2 - 8 * a + 4) ≥ 0 by nlinarith), sq_nonneg (Real.sqrt (a ^ 2 - 8 * a + 4) - (1 : ℝ)), Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      constructor
      · nlinarith [Real.sqrt_nonneg (a ^ 2 - 8 * a + 4), Real.sq_sqrt (show (a ^ 2 - 8 * a + 4) ≥ 0 by nlinarith), sq_nonneg (Real.sqrt (a ^ 2 - 8 * a + 4) - (1 : ℝ)), Real.sqrt_nonneg (3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
      · nlinarith [Real.sqrt_nonneg (a ^ 2 - 8 * a + 4), Real.sq_sqrt (show (a ^ 2 - 8 * a + 4) ≥ 0 by nlinarith)]
    rcases h19 with ⟨y, hy1, hy2, hy3⟩
    use Real.arccos y
    have h14 : sin (Real.arccos y) ^ 2 + a * y - 2 * a = 0 := by
      have h18 : sin (Real.arccos y) ^ 2 = 1 - y ^ 2 := by
        have h10 : sin (Real.arccos y) ^ 2 + y ^ 2 = 1 := by
          have h11 : sin (Real.arccos y) ^ 2 + cos (Real.arccos y) ^ 2 = 1 := Real.sin_sq_add_cos_sq (Real.arccos y)
          have h12 : cos (Real.arccos y) = y := by
            apply Real.cos_arccos
            all_goals linarith [hy1, hy2]
          rw [h12] at h11
          linarith
        linarith
      rw [h18]
      nlinarith [hy3]
    have h15 : sin (Real.arccos y) ^ 2 + a * cos (Real.arccos y) - 2 * a = 0 := by
      have h15 : cos (Real.arccos y) = y := by
        apply Real.cos_arccos
        all_goals linarith [hy1, hy2]
      rw [h15] at *
      linarith [h14]
    simpa using h15
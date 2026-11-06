import Mathlib

theorem algebra_11095 : IsGreatest {s : ℝ | ∃ p q r, p + q + r + s = 8 ∧ p*q + p*r + p*s + q*r + q*s + r*s = 12} (2 + 3*√2) := by
  constructor
  · -- Show that $2 + 3\sqrt{2}$ is achievable.
    use 2 - Real.sqrt 2, 2 - Real.sqrt 2, 2 - Real.sqrt 2
    constructor
    · -- Show that $p + q + r + s = 8$
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
    · -- Show that $pq + pr + p*s + q*r + q*s + r*s = 12$
      nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
  · -- Show that $2 + 3\sqrt{2}$ is greatest.
    intro s hs
    rcases hs with ⟨p, q, r, h1, h2⟩
    nlinarith [sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (q - r), sq_nonneg (s - 2 - 3 * Real.sqrt 2), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num : (2 : ℝ) > 0), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num : (2 : ℝ) ≥ 0)]
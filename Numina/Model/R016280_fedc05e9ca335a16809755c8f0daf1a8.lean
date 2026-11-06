import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_271587 (a : ℝ) :
  (∀ x : ℝ, sin x ^ 6 + cos x ^ 6 + 2 * a * sin x * cos x ≥ 0) ↔ |a| ≤ 1 / 4 := by
  constructor
  · -- (→) Suppose that for all real numbers $x$, the inequality holds, then $|a| \leq \frac{1}{4}$.
    intro h
    have h1 := h (Real.pi / 4)
    have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
    have h3 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    rw [h2, h3] at h1
    have h4 : (Real.sqrt 2 / 2) ^ 6 + (Real.sqrt 2 / 2) ^ 6 + 2 * a * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) ≥ 0 := by
      linarith
    have h5 : (Real.sqrt 2 / 2) ^ 6 = 1 / 8 := by
      calc
        (Real.sqrt 2 / 2) ^ 6 = (Real.sqrt 2) ^ 6 / (2 : ℝ) ^ 6 := by
          field_simp
        _ = ((Real.sqrt 2) ^ 2) ^ 3 / (2 : ℝ) ^ 6 := by
          ring
        _ = (2) ^ 3 / (2 : ℝ) ^ 6 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        _ = (8) / (64) := by
          norm_num
        _ = (1 / 8 : ℝ) := by
          norm_num
    have h6 : (Real.sqrt 2 / 2 : ℝ) ^ 6 + (Real.sqrt 2 / 2 : ℝ) ^ 6 = 1 / 4 := by
      rw [h5]
      norm_num
    have h7 : 2 * a * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = a := by
      ring_nf
      <;> norm_num
      <;> ring
    rw [h6, h7] at h4
    have h2 := h (3 * Real.pi / 4)
    have h9 : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      have h10 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
      rw [h10]
      rw [sin_pi_sub]
      rw [sin_pi_div_four]
    have h11 : cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
      have h12 : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by ring
      rw [h12]
      rw [cos_pi_sub]
      rw [cos_pi_div_four]
      all_goals ring
    rw [h9, h11] at h2
    have h3π4 : (Real.sqrt 2 / 2) ^ 6 + (-Real.sqrt 2 / 2) ^ 6 + 2 * a * (Real.sqrt 2 / 2) * (-Real.sqrt 2 / 2) ≥ 0 := by
      linarith
    have h8 : (Real.sqrt 2 / 2) ^ 6 = 1 / 8 := by
      calc
        (Real.sqrt 2 / 2) ^ 6 = (Real.sqrt 2) ^ 6 / (2 : ℝ) ^ 6 := by
          field_simp
        _ = ((Real.sqrt 2) ^ 2) ^ 3 / (2 : ℝ) ^ 6 := by
          ring
        _ = (2) ^ 3 / (2 : ℝ) ^ 6 := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        _ = (8) / (64) := by
          norm_num
        _ = (1 / 8 : ℝ) := by
          norm_num
    have h12 : (Real.sqrt 2 / 2) ^ 6 + (-Real.sqrt 2 / 2) ^ 6 = 1 / 4 := by
      rw [show (-Real.sqrt 2 / 2 : ℝ) ^ 6 = (Real.sqrt 2 / 2) ^ 6 by ring_nf]
      rw [h8]
      norm_num
    have h13 : 2 * a * (Real.sqrt 2 / 2) * (-Real.sqrt 2 / 2) = -a := by
      ring_nf
      <;> norm_num
      <;> ring
    rw [h12, h13] at h3π4
    have h54 : a ≥ -1 / 4 := by
      linarith
    have h55 : a ≤ 1 / 4 := by
      linarith
    have h53 : -1 / 4 ≤ a ∧ a ≤ 1 / 4 := by
      constructor <;> linarith
    rw [abs_le']
    constructor <;> linarith
  · -- (←) If |a| ≤ 1/4, then the inequality holds for all real numbers $x$.
    intro h x
    have h1 : sin x ^ 2 + cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    have h2 : sin x ^ 6 + cos x ^ 6 = 1 - 3 * (sin x * cos x) ^ 2 := by
      calc
        sin x ^ 6 + cos x ^ 6 = (sin x ^ 2) ^ 3 + (cos x ^ 2) ^ 3 := by ring
        _ = (sin x ^ 2 + cos x ^ 2) ^ 3 - 3 * (sin x ^ 2 * cos x ^ 2) * (sin x ^ 2 + cos x ^ 2) := by ring
        _ = (1) ^ 3 - 3 * (sin x * cos x) ^ 2 * (1) := by
          rw [show sin x ^ 2 + cos x ^ 2 = 1 by linarith [h1]]
          <;> ring
        _ = 1 - 3 * (sin x * cos x) ^ 2 := by
          ring
    have h6 : -1 / 2 ≤ sin x * cos x := by
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2)]
    have h7 : sin x * cos x ≤ 1 / 2 := by
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2)]
    have h54 : -1 / 4 ≤ a := by
      cases' abs_le.mp h with h8 h9
      linarith
    have h55 : a ≤ 1 / 4 := by
      cases' abs_le.mp h with h8 h9
      linarith
    nlinarith [sq_nonneg (a - ( -1 / 4 ) ), sq_nonneg (a - 1 / 4 ), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x * cos x + 1 / 2), h2, h6, h7, sq_nonneg (a * 2 - 1 / 2), sq_nonneg (a * 2 + 1 / 2), mul_self_nonneg (sin x * cos x), mul_self_nonneg (a - 1 / 4 ), mul_self_nonneg (a + 1 / 4 ) ]
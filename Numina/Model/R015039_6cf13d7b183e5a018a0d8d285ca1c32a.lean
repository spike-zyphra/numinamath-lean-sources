import Mathlib

open Real Set
open scoped Real

theorem inequalities_597551 (a : ℝ) :
  (∀ x : ℝ, sin x ^ 6 + cos x ^ 6 + 2 * a * sin x * cos x ≥ 0) ↔ |a| ≤ 1 / 4 := by
  constructor
  · -- First implication: if inequality holds ∀ x, then |a| ≤ 1/4
    intro h
    have h1 := h (Real.pi / 4)
    have h2 := h (3 * Real.pi / 4)
    have h3 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [sin_pi_div_four]
      <;> linarith
    have h4 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
      rw [cos_pi_div_four]
    have h5 : sin (3 * Real.pi / 4) = Real.sqrt 2 / 2 := by
      have : sin (3 * Real.pi / 4) = sin (Real.pi - (Real.pi / 4)) := by
        ring_nf
      rw [this]
      rw [sin_pi_sub]
      rw [sin_pi_div_four]
      <;> linarith
    have h6 : cos (3 * Real.pi / 4) = - Real.sqrt 2 / 2 := by
      have : cos (3 * Real.pi / 4) = - cos (Real.pi / 4) := by
        have : 3 * Real.pi / 4 = Real.pi - (Real.pi / 4) := by
          ring_nf
        rw [this]
        rw [cos_pi_sub]
        <;> linarith
      rw [this, cos_pi_div_four]
      <;> linarith
    rw [h3, h4] at h1
    rw [h5, h6] at h2
    have h8 : (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 / 2 := by
      have h : Real.sqrt 2 ^ 2 = 2 := by
        exact Real.sq_sqrt (by linarith)
      linarith
    have h9 : (Real.sqrt 2 / 2 : ℝ) ^ 6 = 1 / 8 := by
      calc
        (Real.sqrt 2 / 2 : ℝ) ^ 6
            = ((Real.sqrt 2 / 2 : ℝ) ^ 2) ^ 3 := by ring_nf
        _ = (1 / 2) ^ 3 := by rw [h8]
        _ = (1 / 8 : ℝ) := by norm_num
    have ha1 : a ≤ 1 / 4 := by
      nlinarith [h2, h9, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have ha2 : -1 / 4 ≤ a := by
      nlinarith [h1, h9, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [abs_le]
    constructor
    · -- - (1 / 4) ≤ a
      linarith
    · -- a ≤ (1 / 4 : ℝ)
      nlinarith
  · -- Now the reverse. Assume |a| <= 1/4. Prove inequality holds ∀ x : ℝ
    intro ha x
    have h1 : |a| ≤ 1 / 4 := ha
    have h5 : - (1 : ℝ)/ 4 ≤ a := by
      linarith [abs_le.mp h1]
    have h6 : a ≤ (1 : ℝ)/ 4 := by
      linarith [abs_le.mp h1]
    have h1 : sin x ^ 6 + cos x ^ 6 + 2 * a * sin x * cos x ≥ 0 := by
      nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x * cos x), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), Real.sin_sq_add_cos_sq x, sq_nonneg (a - (1/4)), sq_nonneg (a + (1/4))]
    simpa using h1
import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_242223 (a : ℝ) :
  (∀ x : ℝ, cos (2 * x) + 2 * a * cos x + 7 ≥ 0) ↔ a ∈ Icc (-4) 4 := by
  constructor
  · -- Forward: Assume that the inequality holds for all x, prove a ∈ [-4, 4]
    intro h
    have h1 := h 0
    have h2 : cos (2 * (0 : ℝ)) + 2 * a * cos (0 : ℝ) + 7 ≥ 0 := h1
    have h3 : cos (2 * (0 : ℝ)) = 1 := by
      simp
    have h4 : cos (0 : ℝ) = 1 := by
      simp
    rw [h3, h4] at h2
    have h5 : a ≥ -4 := by
      nlinarith
    have h6 := h (Real.pi)
    have h7 : cos (2 * Real.pi) + 2 * a * cos Real.pi + 7 ≥ 0 := h6
    have h8 : cos (2 * Real.pi) = 1 := by
      exact Real.cos_two_pi
    have h10 : cos Real.pi = -1 := by
      exact Real.cos_pi
    rw [h8, h10] at h7
    have h11 : a ≤ 4 := by
      nlinarith
    constructor
    · linarith
    · linarith
  · -- Reverse: Assume a ∈ [-4, 4], prove the inequality holds for all x
    rintro ⟨ha1, ha2⟩
    intro x
    have h1 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
      rw [cos_two_mul]
    rw [h1]
    have h8 : -1 ≤ cos x := by
      linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    have h9 : cos x ≤ 1 := by
      linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos x - 1), sq_nonneg (cos x + a / 2), sq_nonneg (cos x - (-a / 2)), sq_nonneg (2 * cos x + a), sq_nonneg (2 * cos x - 4), sq_nonneg (2 * cos x + 4), Real.cos_sq_add_sin_sq x, Real.sin_sq x]
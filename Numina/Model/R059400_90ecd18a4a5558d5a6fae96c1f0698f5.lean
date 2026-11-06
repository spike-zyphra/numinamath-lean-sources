import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_188786 {x : ℝ} (hx : x > 0) :
    cos (8 * π * x) + 2 * cos (4 * π * x) - cos (2 * π * x) +
    2 * sin (π * x) + 3 = 0 ↔
    2 * (cos (4 * π * x) + 1 / 2) ^ 2 + 2 * (sin (π * x) + 1 / 2) ^ 2 = 0 := by
  have h1 : cos (8 * π * x) = 2 * cos (4 * π * x) ^ 2 - 1 := by
    have h2 : cos (8 * π * x) = cos (2 * (4 * π * x)) := by ring_nf
    rw [h2]
    rw [cos_two_mul]
  have h3 : cos (2 * π * x) = 1 - 2 * sin (π * x) ^ 2 := by
    have h4 : cos (2 * π * x) = cos (2 * (π * x)) := by ring_nf
    rw [h4]
    rw [cos_two_mul]
    rw [sin_sq]
    ring_nf
  constructor
  · -- Assume the original equation, prove the squared form
    intro h
    rw [h1, h3] at h
    nlinarith [sq_nonneg (cos (4 * π * x) + 1 / 2), sq_nonneg (sin (π * x) + 1 / 2), sq_nonneg (cos (4 * π * x) - -1 / 2), sq_nonneg (sin (π * x) - -1 / 2)]
  · -- Assume the squared form, prove the original equation
    intro h
    rw [h1, h3]
    have hcos : cos (4 * π * x) + 1 / 2 = 0 := by
      nlinarith [sq_nonneg (cos (4 * π * x) + 1 / 2), sq_nonneg (sin (π * x) + 1 / 2)]
    have hsin : sin (π * x) + 1 / 2 = 0 := by
      nlinarith [sq_nonneg (cos (4 * π * x) + 1 / 2), sq_nonneg (sin (π * x) + 1 / 2)]
    nlinarith [hcos, hsin, sq_nonneg (cos (4 * π * x) - -1 / 2), sq_nonneg (sin (π * x) - -1 / 2)]
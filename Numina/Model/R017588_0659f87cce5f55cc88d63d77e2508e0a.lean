import Mathlib

open Real Set
open scoped Real

theorem algebra_225543 (φ : ℝ) :
  3 * sin φ * cos φ + 4 * sin φ + 3 * (cos φ)^2 = 4 + cos φ ↔
  (3 * sin φ - 1) * (cos φ - sin φ + 1) = 0 := by
  constructor
  · -- Assume the original equation, prove the factored form
    intro h
    have h1 : (sin φ) ^ 2 + (cos φ) ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
    have eq1 : 3 * (cos φ) ^ 2 - 4 - cos φ = -3 * (sin φ) ^ 2 - cos φ - 1 := by
      have h2 : (sin φ) ^ 2 = 1 - (cos φ) ^ 2 := by
        linarith [h1]
      nlinarith [h2]
    have h2 : (3 * sin φ * cos φ + 4 * sin φ + 3 * (cos φ) ^ 2 - 4 - cos φ) = 0 := by linarith [h]
    have h3 : (3 * sin φ * cos φ - 3 * (sin φ) ^ 2 + 4 * sin φ - cos φ - 1) = 0 := by
      nlinarith [h2, eq1]
    linarith [h3]
  · -- Assume the factored form, prove the original equation
    intro h
    have h1 : (sin φ) ^ 2 + (cos φ) ^ 2 = 1 := Real.sin_sq_add_cos_sq φ
    have h2 : (3 * sin φ * cos φ - 3 * (sin φ) ^ 2 + 4 * sin φ - cos φ - 1) = 0 := by
      have h3 : (3 * sin φ - 1) * (cos φ - sin φ + 1) = 0 := h
      nlinarith [h3]
    have eq1 : (3 * (cos φ) ^ 2 - 4 - cos φ) = (-3 * (sin φ) ^ 2 - cos φ - 1) := by
      have h2 : (sin φ) ^ 2 = 1 - (cos φ) ^ 2 := by
        linarith [h1]
      nlinarith [h2]
    have h3 : (3 * sin φ * cos φ + 4 * sin φ + 3 * (cos φ) ^ 2 - 4 - cos φ) = 0 := by
      nlinarith [h2, eq1]
    linarith [h3]
import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156007 {f : ℝ → ℝ} (hf : f = λ x => (x^2 - 1)/x) :
    MonotoneOn f (Set.Iio 0) ∧ MonotoneOn f (Set.Ioi 0) := by
  constructor
  · -- Prove that f is monotone on Iio 0
    intro x hx y hy hxy
    have h1 : x < (0 : ℝ) := hx
    have h2 : y < (0 : ℝ) := hy
    rw [hf]
    have h3 : x ≤ y := hxy
    have h4 : x < 0 := by linarith
    have h5 : y < 0 := by linarith
    have h6 : x ≤ y := h3
    have h7 : (x ^ 2 - 1) / x ≤ (y ^ 2 - 1) / y := by
      have h4 : x < 0 := by linarith
      have h5 : y < 0 := by linarith
      have h8 : x * y > 0 := by nlinarith
      have h11 : (y ^ 2 - 1) / y - (x ^ 2 - 1) / x ≥ 0 := by
        have h12 : (y ^ 2 - 1) / y - (x ^ 2 - 1) / x = ((y - x) * (x * y + 1)) / (x * y) := by
          field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith), (show x * y ≠ 0 by nlinarith)]
          ring
        rw [h12]
        apply div_nonneg
        have h13 : y - x ≥ 0 := by linarith
        have h14 : x * y + 1 > 0 := by nlinarith
        have h15 : (y - x) * (x * y + 1) ≥ 0 := by
          nlinarith
        linarith
        have h7 : x * y > 0 := h8
        all_goals nlinarith
      linarith
    simpa using h7
  · -- Prove that f is monotone on Ioi 0
    intro x hx y hy hxy
    have h1 : 0 < x := hx
    have h2 : 0 < y := hy
    rw [hf]
    have h3 : x ≤ y := hxy
    have h4 : 0 < x := h1
    have h5 : 0 < y := h2
    have h6 : x ≤ y := h3
    have h7 : (x ^ 2 - 1) / x ≤ (y ^ 2 - 1) / y := by
      have h4 : 0 < x := h1
      have h5 : 0 < y := h2
      have h8 : x * y > 0 := by nlinarith
      have h11 : (y ^ 2 - 1) / y - (x ^ 2 - 1) / x ≥ 0 := by
        have h12 : (y ^ 2 - 1) / y - (x ^ 2 - 1) / x = ((y - x) * (x * y + 1)) / (x * y) := by
          field_simp [(show x ≠ 0 by linarith), (show y ≠ 0 by linarith), (show x * y ≠ 0 by nlinarith)]
          ring
        rw [h12]
        apply div_nonneg
        have h13 : y - x ≥ 0 := by linarith
        have h14 : x * y + 1 > 0 := by nlinarith
        have h15 : (y - x) * (x * y + 1) ≥ 0 := by
          nlinarith
        linarith
        have h7 : x * y > 0 := h8
        all_goals nlinarith
      linarith
    simpa using h7
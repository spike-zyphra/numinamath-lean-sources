import Mathlib

open Polynomial

theorem algebra_5455 {x : ℂ} (hx : x^4 + x^3 + x^2 + x + 1 = 0) :
    x + 1/x = (-(1 : ℂ) + Real.sqrt 5)/2 ∨ x + 1/x = (-(1 : ℂ) - Real.sqrt 5)/2 := by
  have h1 : x ≠ 0 := by
    by_contra h
    rw [h] at hx
    norm_num at hx

  have eq1 : x ^ 2 + x + 1 + 1 / x + 1 / x ^ 2 = 0 := by
    have h2 : x^4 + x^3 + x^2 + x + 1 = 0 := hx
    have h3 : x ≠ 0 := h1
    have eq2 : (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) / x ^ 2 = 0 := by
      rw [h2]
      norm_num
    have eq3 : (x ^ 4 + x ^ 3 + x ^ 2 + x + 1) / x ^ 2 = x ^ 2 + x + 1 + 1 / x + 1 / x ^ 2 := by
      field_simp [h1]
      <;> ring
    rw [eq3] at eq2
    simpa using eq2

  have eq2 : (x + 1 / x) ^ 2 + (x + 1 / x) - 1 = 0 := by
    have h5 : x ^ 2 + x + 1 + 1 / x + 1 / x ^ 2 = 0 := eq1
    have eq4 : x ^ 2 + x + 1 + 1 / x + 1 / x ^ 2 = (x + 1 / x) ^ 2 + (x + 1 / x) - 1 := by
      have eq3 : x ^ 2 + 1 / x ^ 2 = (x + 1 / x) ^ 2 - 2 := by
        field_simp [h1]
        <;> ring
      have eq6 : x ^ 2 + x + 1 + 1 / x + 1 / x ^ 2 = (x ^ 2 + 1 / x ^ 2) + (x + 1 / x) + 1 := by
        field_simp [h1]
        <;> ring
      rw [eq6, eq3]
      all_goals ring
    rw [eq4] at h5
    simpa using h5

  have h8 : (x + 1/x - (-(1 : ℂ) + Real.sqrt 5)/2) * (x + 1/x - (-(1 : ℂ) - Real.sqrt 5)/2) = 0 := by
    have h9 : (x + 1 / x) ^ 2 + (x + 1 / x) - 1 = 0 := eq2
    ring_nf at h9 ⊢
    simp [Complex.ext_iff, pow_two, mul_add, mul_sub] at h9 ⊢
    constructor
    · nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

  cases' (mul_eq_zero.1 h8) with h11 h12
  · -- First case
    left
    exact eq_of_sub_eq_zero h11
  · -- Second case
    right
    exact eq_of_sub_eq_zero h12
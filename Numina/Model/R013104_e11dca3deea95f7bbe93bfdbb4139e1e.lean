import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_126975 (r : ℝ) (hr : r = 10) (v : ℝ) (h : v = 1000) :
    ∃ t, t > 0 ∧ v * t = r * sqrt (1 + (t / r)^2) := by
  rw [hr, h]
  use Real.sqrt (100 / 999999)
  constructor
  · -- Show that t is positive
    positivity
  · -- Show that v * t = r * sqrt (1 + (t / r)^2)
    have h1 : Real.sqrt (100 / 999999) ^ 2 = 100 / 999999 := Real.sq_sqrt (show 0 ≤ (100 / 999999 : ℝ) by norm_num)
    have h2 : Real.sqrt (1 + (Real.sqrt (100 / 999999) / (10 : ℝ)) ^ 2) = Real.sqrt (1000000 / 999999) := by
      have h3 : (Real.sqrt (100 / 999999) / (10 : ℝ)) ^ 2 = 1 / 999999 := by
        calc
          (Real.sqrt (100 / 999999) / (10 : ℝ)) ^ 2
              = (Real.sqrt (100 / 999999) ^ 2) / (100 : ℝ) := by ring_nf
          _   = (100 / 999999 : ℝ) / (100 : ℝ) := by rw [h1]
          _   = 1 / 999999 := by norm_num
      rw [h3]
      have h4 : (1: ℝ) + (1 / 999999) = 1000000 / 999999 := by norm_num
      rw [h4]
    have h5 : Real.sqrt (1000000 / 999999) = (1000 / Real.sqrt (999999 : ℝ)) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h7 : Real.sqrt (100 / 999999) = (10 / Real.sqrt (999999 : ℝ)) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf
      <;> norm_num
    have h8 : (1000 : ℝ) * Real.sqrt (100 / 999999) = (10000 / Real.sqrt (999999 : ℝ)) := by
      rw [h7]
      field_simp
      <;> ring_nf
    have h9 : (10 * Real.sqrt (1000000 / 999999) : ℝ) = (10000 / Real.sqrt (999999 : ℝ)) := by
      rw [h5]
      field_simp
      <;> ring_nf
    rw [h2, h9]
    linarith [h8]
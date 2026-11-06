import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_109235 (f : ℝ → ℝ) (a : ℝ) (ha : a > 0)
  (h₀ : ∀ x, f x = sqrt (x ^ 2 + 1) - 2 / 5 * a * x)
  (h₁ : MonotoneOn f (Ici 0)) :
  5 / 2 ≤ a := by
  by_contra h
  push_neg at h
  have ha2 : a < 5 / 2 := by linarith
  have h2 : 0 < a := ha
  have h3 : 0 < (4 / 25) * a ^ 2 := by nlinarith [sq_pos_of_pos ha]
  have h4 : (1 + (4 / 25) * a ^ 2) ^ 2 > ( (4 / 25) * a ^ 2 + 1 ) := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos (show 0 < a ^ 2 by nlinarith)]
  have h5 : (4 / 25 : ℝ) * a ^ 2 + 1 ≥ 0 := by nlinarith
  have h6 : (1 + (4 / 25) * a ^ 2) > Real.sqrt ((4 / 25) * a ^ 2 + 1) := by
    have h6 : Real.sqrt ((4 / 25) * a ^ 2 + 1) ^ 2 = (4 / 25) * a ^ 2 + 1 := by
      rw [Real.sq_sqrt]
      positivity
    have h7 : Real.sqrt ((4 / 25) * a ^ 2 + 1) ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg ((4 / 25) * a ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 / 25) * a ^ 2 + 1 by positivity)]
  have h7 : (1 : ℝ) > Real.sqrt ((4 / 25) * a ^ 2 + 1) - (4 / 25) * a ^ 2 := by
    linarith [h6]
  have h8 : (0 : ℝ) ≥ 0 := by norm_num
  have h10 : f 0 ≤ f (2 / 5 * a) := by
    apply h₁
    · -- Show 0 ∈ Ici 0
      simp
    · -- Show 2/5*a ∈ Ici 0
      have : (2 / 5 * a) ≥ 0 := by nlinarith
      simp [this]
    · -- Show 0 ≤ 2/5*a
      nlinarith [show 0 < a by linarith]
  have h11 : f 0 = 1 := by
    rw [h₀ 0]
    norm_num [Real.sqrt_one]
  have h14 : f (2 / 5 * a) = Real.sqrt ((4 / 25) * a ^ 2 + 1) - (4 / 25) * a ^ 2 := by
    rw [h₀ (2 / 5 * a)]
    have h13 : Real.sqrt ((2 / 5 * a) ^ 2 + 1) = Real.sqrt ((4 / 25) * a ^ 2 + 1) := by
      ring_nf
    rw [h13]
    ring
  rw [h11, h14] at h10
  nlinarith [h7, Real.sqrt_nonneg ((4 / 25) * a ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ (4 / 25) * a ^ 2 + 1 by positivity)]
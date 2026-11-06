import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_11439 {f : ℝ → ℝ}
  (hf : f = λ x => 4 * sin x * (sin (π / 4 + x / 2))^2 + cos (2 * x))
  (A B : Set ℝ)
  (hA : A = {x | π / 6 ≤ x ∧ x ≤ 2 * π / 3})
  (hB : B = {x | abs (f x - m) < 2})
  (hAB : A ∪ B = B) :
  1 < m ∧ m < 4 := by
  have h1 : A ⊆ B := by
    rw [Set.union_eq_right] at hAB
    exact hAB

  have h2 : (π / 6) ∈ A := by
    rw [hA]
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

  have h3 : (π / 6) ∈ B := h1 h2

  have h4 : (π / 2) ∈ A := by
    rw [hA]
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h5 : (π / 2) ∈ B := h1 h4

  have h6 : (2 * π / 3) ∈ A := by
    rw [hA]
    constructor
    · linarith [Real.pi_pos]
    · linarith [Real.pi_pos]

  have h7 : (2 * π / 3) ∈ B := h1 h6
  have h8 : abs (f (π / 6) - m) < 2 := by
    rw [hB] at h3
    exact h3
  have h9 : abs (f (π / 2) - m) < 2 := by
    rw [hB] at h5
    exact h5
  have h10 : abs (f (2 * π / 3) - m) < 2 := by
    rw [hB] at h7
    exact h7
  have h11 : f (π / 6) = 2 := by
    rw [hf]
    have h1 : sin (π / 4 + (π / 6) / 2) = Real.sqrt 3 / 2 := by
      have h1 : π / 4 + (π / 6) / 2 = π / 3 := by
        linarith [Real.pi_pos]
      rw [h1]
      exact sin_pi_div_three
    simp [h1]
    have h2 : sin (π / 6) = 1 / 2 := sin_pi_div_six
    have h3 : cos (2 * (π / 6)) = 1 / 2 := by
      have h1 : 2 * (π / 6) = π / 3 := by ring
      rw [h1]
      exact cos_pi_div_three
    norm_num [h2, h3]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith)]
  have h14 : f (π / 2) = 3 := by
    rw [hf]
    have h1 : sin (π / 4 + (π / 2) / 2) = 1 := by
      have h1 : π / 4 + (π / 2) / 2 = π / 2 := by
        linarith [Real.pi_pos]
      rw [h1]
      exact sin_pi_div_two
    have h2 : sin (π / 2) = 1 := sin_pi_div_two
    have h3 : cos (2 * (π / 2)) = -1 := by
      have h1 : 2 * (π / 2) = π := by ring
      rw [h1]
      exact cos_pi
    simp [h1, h2, h3]
    all_goals norm_num
  constructor
  · -- Show 1 < m
    have h3' : -2 < f (π / 2) - m := by linarith [abs_lt.mp h9]
    have h4' : f (π / 2) - m < 2 := by linarith [abs_lt.mp h9]
    rw [h14] at h3' h4'
    linarith
  · -- Show m < 4
    have h3' : -2 < f (π / 6) - m := by linarith [abs_lt.mp h8]
    have h4' : f (π / 6) - m < 2 := by linarith [abs_lt.mp h8]
    rw [h11] at h3' h4'
    linarith
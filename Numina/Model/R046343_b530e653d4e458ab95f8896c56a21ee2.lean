import Mathlib

theorem inequalities_143807 (a b c : ℝ)
(h : ∀ x : ℝ, a * x^2 + b * x + c ≥ b * x^2 + c * x + a ∧ b * x^2 + c * x + a ≥ c * x^2 + a * x + b) :
    a = b ∧ b = c := by

  have h1 := h 0
  have h2 : a * (0:ℝ)^2 + b * (0:ℝ) + c ≥ b * (0:ℝ)^2 + c * (0:ℝ) + a := by
    linarith [h1.1]
  have h3 : c ≥ a := by
    nlinarith
  have h4 : b * (0:ℝ)^2 + c * (0:ℝ) + a ≥ c * (0:ℝ)^2 + a * (0:ℝ) + b := by
    linarith [h1.2]
  have h5 : a ≥ b := by
    nlinarith
  have h9 := h (-1)
  have h10 : a * (-1:ℝ)^2 + b * (-1:ℝ) + c ≥ b * (-1:ℝ)^2 + c * (-1:ℝ) + a := by
    linarith [h9.1]
  have h11 : c ≥ b := by
    nlinarith
  have h12 : b * (-1:ℝ)^2 + c * (-1:ℝ) + a ≥ c * (-1:ℝ)^2 + a * (-1:ℝ) + b := by
    linarith [h9.2]
  have h13 : a ≥ c := by
    nlinarith
  have h14 : a = c := by
    linarith
  have h18 := h 2
  have h19 : a * (2:ℝ)^2 + b * (2:ℝ) + c ≥ b * (2:ℝ)^2 + c * (2:ℝ) + a := by
    linarith [h18.1]
  have h20 : b * (2:ℝ)^2 + c * (2:ℝ) + a ≥ c * (2:ℝ)^2 + a * (2:ℝ) + b := by
    linarith [h18.2]
  have h21 : b = c := by
    nlinarith [h14, h19, h20]
  constructor
  · -- Show a = b
    nlinarith [h14, h21]
  · -- Show b = c
    linarith [h21]
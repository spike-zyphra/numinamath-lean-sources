import Mathlib

open Real Set
open scoped Real

theorem inequalities_222545 (θ : ℝ) (x y : ℝ)
  (h : (x * cos θ + y * sin θ)^2 + x * sin θ - y * cos θ = 1) :
  x^2 + y^2 ≥ 3 / 4 := by

  have h1 : cos θ ^ 2 + sin θ ^ 2 = 1 := by 
    exact Real.cos_sq_add_sin_sq θ

  have h2 : x^2 + y^2 = (x * cos θ + y * sin θ)^2 + (x * sin θ - y * cos θ)^2 := by
    ring_nf
    <;> simp [Real.cos_sq, Real.sin_sq]
    <;> nlinarith

  have eq1 : x * sin θ - y * cos θ = 1 - (x * cos θ + y * sin θ) ^ 2 := by 
    linarith [h]

  have eq2 : x^2 + y^2 = (x * cos θ + y * sin θ)^2 + (1 - (x * cos θ + y * sin θ)^2)^2 := by 
    rw [h2]
    rw [eq1]
    <;> ring

  have h3 : (x * cos θ + y * sin θ)^2 + (1 - (x * cos θ + y * sin θ)^2)^2 ≥ 3 / 4 := by 
    nlinarith [sq_nonneg ((x * cos θ + y * sin θ) ^ 2 - 1 / 2), sq_nonneg ((x * cos θ + y * sin θ) ^ 2 - 1 / 2), sq_nonneg ((x * cos θ + y * sin θ) ^ 2 - 1), sq_nonneg ((x * cos θ + y * sin θ) ^ 2 - 1), sq_nonneg (1 - (x * cos θ + y * sin θ) ^ 2 - 1 / 2), sq_nonneg (x * cos θ + y * sin θ), sq_nonneg ((x * cos θ + y * sin θ) ^ 2 - 1 / 2), sq_nonneg (1 - (x * cos θ + y * sin θ) ^ 2 - 1 / 2), sq_nonneg (x * cos θ * y * sin θ), h1, h, sq_nonneg (x * cos θ + y * sin θ), sq_nonneg (x * sin θ - y * cos θ)]

  linarith [eq2, h3]
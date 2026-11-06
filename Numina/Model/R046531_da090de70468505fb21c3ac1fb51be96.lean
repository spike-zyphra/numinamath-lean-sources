import Mathlib

open Real
open scoped BigOperators

theorem inequalities_47271 (a b c : ℝ) (p : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : a + c > b)
  (h₃ : b + c > a)
  (h₄ : p = (a + b + c) / 2) :
  2 * sqrt ((p - b) * (p - c)) ≤ a := by

  have ha : 0 < a := h₀.1
  have hb : 0 < b := h₀.2.1
  have hc : 0 < c := h₀.2.2

  have h9 : (p - b) * (p - c) ≥ 0 := by
    have h10 : p - b ≥ 0 := by
      nlinarith
    have h11 : p - c ≥ 0 := by
      nlinarith
    nlinarith

  have h13 : 4 * ((p - b) * (p - c)) ≤ a ^ 2 := by
    rw [show p = (a + b + c) / 2 by linarith [h₄]]
    have h14 : ( ((a + b + c) / 2 - b) * ((a + b + c) / 2 - c) ) =
      ((a - b + c) / 2) * ((a + b - c) / 2) := by ring
    rw [h14]
    nlinarith [sq_nonneg (a - b + c), sq_nonneg (a + b - c), 
      sq_nonneg (a^2), sq_nonneg ((a - b) + (a - c)), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
      mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
      mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
      mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₁), 
      sq_nonneg (b - c)
    ]

  have h14 : (2 * sqrt ((p - b) * (p - c))) ^ 2 ≤ a ^ 2 := by
    have h15 : Real.sqrt ((p - b) * (p - c)) ^ 2 = (p - b) * (p - c) := Real.sq_sqrt (show (p - b) * (p - c) ≥ 0 by nlinarith)
    nlinarith [Real.sqrt_nonneg ((p - b) * (p - c)), h13, h15]

  have h16 : 2 * Real.sqrt ((p - b) * (p - c)) ≥ 0 := by nlinarith [Real.sqrt_nonneg ((p - b) * (p - c))]

  nlinarith [Real.sqrt_nonneg ((p - b) * (p - c)), Real.sq_sqrt (show (p - b) * (p - c) ≥ 0 by nlinarith), sq_nonneg (2 * Real.sqrt ((p - b) * (p - c)) - a), sq_nonneg (a - 2 * Real.sqrt ((p - b) * (p - c))), mul_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) (show (0 : ℝ) ≤ Real.sqrt ((p - b) * (p - c)) by apply Real.sqrt_nonneg), h14]
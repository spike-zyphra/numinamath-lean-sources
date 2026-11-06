import Mathlib

open Real
open scoped BigOperators

theorem inequalities_155063 (a b c s : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a + b > c)
  (h₂ : a + c > b)
  (h₃ : b + c > a)
  (h₄ : s = (a + b + c) / 2) :
  4 * s ≤ a * b / (s - c) + b * c / (s - a) + c * a / (s - b) := by

  have h5 : s - c = (a + b - c) / 2 := by
    rw [h₄]
    ring

  have h6 : s - a = (b + c - a) / 2 := by
    rw [h₄]
    ring

  have h7 : s - b = (a + c - b) / 2 := by
    rw [h₄]
    ring

  have h8 : 0 < s - c := by
    rw [h5]
    nlinarith

  have h9 : 0 < s - a := by
    rw [h6]
    nlinarith

  have h10 : 0 < s - b := by
    rw [h7]
    nlinarith

  rw [show 4 * s = 2 * (a + b + c) by
    linarith [h₄]
  ]

  have h11 : a * b / (s - c) = 2 * (a * b / (a + b - c)) := by
    rw [h5]
    field_simp [(show a + b - c ≠ 0 by linarith)]
    <;> ring

  have h12 : b * c / (s - a) = 2 * (b * c / (b + c - a)) := by
    rw [h6]
    field_simp [(show b + c - a ≠ 0 by linarith)]
    <;> ring

  have h13 : c * a / (s - b) = 2 * (c * a / (a + c - b)) := by
    rw [h7]
    field_simp [(show a + c - b ≠ 0 by nlinarith)]
    <;> ring

  rw [h11, h12, h13]

  have h14 : a * b / (a + b - c) + b * c / (b + c - a) + c * a / (a + c - b) ≥ a + b + c := by

    have h15 : 0 < a + b - c := by nlinarith

    have h16 : 0 < b + c - a := by nlinarith

    have h17 : 0 < a + c - b := by nlinarith

    have h18 : a * b / (a + b - c) + b * c / (b + c - a) + c * a / (a + c - b) - (a + b + c) ≥ 0 := by

      have h19 : a * b / (a + b - c) + b * c / (b + c - a) + c * a / (a + c - b) - (a + b + c) =
          ( a * b * (b + c - a) * (a + c - b) + b * c * (a + b - c) * (a + c - b) + c * a * (a + b - c) * (b + c - a) - (a + b + c) * (a + b - c) * (b + c - a) * (a + c - b) ) / ( (a + b - c) * (b + c - a) * (a + c - b) ) := by 
        field_simp
        ring

      rw [h19] at *

      apply div_nonneg

      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (a + c - b),
          mul_pos h₀.1 h₀.2.1, mul_pos h₀.2.1 h₀.2.2, mul_pos h₀.1 h₀.2.2,
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), 
          mul_pos (sub_pos.mpr h₂) (sub_pos.mpr h₃), 
          mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₃)
      ]

      positivity

    linarith

  linarith [h14]
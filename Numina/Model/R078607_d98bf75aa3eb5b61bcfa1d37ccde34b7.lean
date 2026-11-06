import Mathlib

open Real
open scoped BigOperators

theorem inequalities_107690 (a b c d e : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e)
  (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a)
  (h₄ : d + e > a) (h₅ : d + a > e) (h₆ : e + a > d)
  (h₇ : b + d > e) (h₈ : b + e > d) (h₉ : d + e > b) :
  (1/2) * a * b + (1/2) * a * c + (1/2) * b * c + (1/2) * d * e +
  (1/2) * d * a + (1/2) * e * a + (1/2) * b * d + (1/2) * c * e +
  (1/2) * a * b + (1/2) * a * c + (1/2) * b * c + (1/2) * d * e +
  (1/2) * d * a + (1/2) * e * a + (1/2) * b * d + (1/2) * c * e >
  (1/2) * (a * b + a * c + b * c + d * e + d * a + e * a + b * d + c * e) := by
  ring_nf
  nlinarith [h₀.left, h₀.right.left, h₀.right.right.left, h₀.right.right.right.left, h₀.right.right.right.right,
            mul_pos h₀.left h₀.right.left, mul_pos h₀.left h₀.right.right.left, mul_pos h₀.left h₀.right.right.right.left, mul_pos h₀.left h₀.right.right.right.right,
            mul_pos h₀.right.left h₀.right.right.left, mul_pos h₀.right.left h₀.right.right.right.left, mul_pos h₀.right.left h₀.right.right.right.right,
            mul_pos h₀.right.right.left h₀.right.right.right.left, mul_pos h₀.right.right.left h₀.right.right.right.right,
            mul_pos h₀.right.right.right.left h₀.right.right.right.right
           ]
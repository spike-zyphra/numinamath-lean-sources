import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem inequalities_1103
  (a b c : ℝ)
  (h₀ : 0 < a)
  (h₁ : 0 < b)
  (h₂ : 0 < c)
  (h₃ : a < 1)
  (h₄ : b < 1)
  (h₅ : c < 1)
  (h₆ : 2 * (a + b + c) + 4 * a * b * c = 3 * (a * b + b * c + c * a) + 1) :
  3 / 4 ≥ a + b + c := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂,
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄),
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₅),
          mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅),
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄),
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₅),
          mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅)]
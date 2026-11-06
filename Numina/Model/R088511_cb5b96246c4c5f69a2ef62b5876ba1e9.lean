import Mathlib

open Nat

theorem algebra_5214 {x : ℝ} (hx : 0 < x) (h : x^2 - 1 / x^2 = 6) : x^4 + 1 / x^4 = 38 := by
  have h1 : x^4 + 1 / x^4 = (x^2 - 1 / x^2) ^ 2 + 2 := by
    field_simp
    <;> ring
  rw [h1, h]
  all_goals norm_num
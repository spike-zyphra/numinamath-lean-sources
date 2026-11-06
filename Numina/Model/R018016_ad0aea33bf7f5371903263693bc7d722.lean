import Mathlib

open Polynomial

theorem algebra_4719 (x : ℕ) (hx : 0 < x) (h : 1 / (10 * x : ℚ) = 1 / (x ^ 2 + x : ℚ) + 1 / (x ^ 2 + 3 * x + 2 : ℚ) + 1 / (x ^ 2 + 5 * x + 6 : ℚ)) : x = 27 := by 
  have h1 : (x : ℚ) > 0 := by
    exact_mod_cast (show (x) > 0 by linarith)
  have hx2 : (x : ℚ) > 0 := h1
  have hx21 : (x + 1 : ℚ) > 0 := by linarith
  have hx22 : (x + 2 : ℚ) > 0 := by linarith
  have hx23 : (x + 3 : ℚ) > 0 := by linarith
  have eq3 : (1 / (x ^ 2 + x : ℚ) + 1 / (x ^ 2 + 3 * x + 2 : ℚ) + 1 / (x ^ 2 + 5 * x + 6 : ℚ) ) =
    (1 / (x : ℚ) - 1 / (x + 3 : ℚ)) := by 
    have h2 : (x ^ 2 + x : ℚ) = (x : ℚ) * (x + 1 : ℚ) := by ring
    have h3 : (x ^ 2 + 3 * x + 2 : ℚ) = (x + 1 : ℚ) * (x + 2 : ℚ) := by ring
    have h4 : (x ^ 2 + 5 * x + 6 : ℚ) = (x + 2 : ℚ) * (x + 3 : ℚ) := by ring
    rw [h2, h3, h4]
    have hx5 : (x : ℚ) ≠ 0 := by nlinarith
    have hx6 : (x + 1 : ℚ) ≠ 0 := by nlinarith
    have hx7 : (x + 2 : ℚ) ≠ 0 := by nlinarith
    have hx8 : (x + 3 : ℚ) ≠ 0 := by nlinarith
    field_simp [hx5, hx6, hx7, hx8]
    <;> ring
  have eq4 : (1 / (10 * x : ℚ) : ℚ) = (1 / (x : ℚ) - 1 / (x + 3 : ℚ) ) := by
    linarith [h, eq3]
  have eq5 : (x : ℚ) = 27 := by
    have hx5 : (x : ℚ) > 0 := h1
    have hx6 : (x + 3 : ℚ) > 0 := by linarith
    field_simp [(show (x : ℚ) ≠ 0 by nlinarith), (show (x + 3 : ℚ) ≠ 0 by nlinarith)] at eq4 ⊢
    nlinarith
  have h27 : x = 27 := by
    exact_mod_cast eq5
  exact h27
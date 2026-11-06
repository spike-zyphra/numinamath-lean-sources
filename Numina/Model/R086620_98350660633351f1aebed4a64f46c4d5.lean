import Mathlib

open Polynomial

theorem algebra_3151 {a b c : ℝ} (ha : a ≠ 0) (f : ℝ → ℝ)
    (hf : ∀ x, f x = a * x ^ 2 + b * x + c) (h2 : f 2 = 20) (h4 : f 4 = 55)
    (h10 : f 10 = 304) : f 5 = 81 + 1 / 2 := by

  have eq1 : a * 2^2 + b * 2 + c = 20 := by
    rw [hf] at h2
    linarith
  have eq2 : a * 4^2 + b * 4 + c = 55 := by
    rw [hf] at h4
    linarith
  have eq3 : a * 10^2 + b * 10 + c = 304 := by
    rw [hf] at h10
    linarith
  have eq4 : 12 * a + 2 * b = 35 := by 
    linarith [eq1, eq2]
  have eq5 : 84 * a + 6 * b = 249 := by
    linarith [eq2, eq3]
  have eq6 : 36 * a + 6 * b = 105 := by
    linarith [eq4]
  have ha2 : a = 3 := by
    linarith [eq5, eq6]
  have hb : b = -1 / 2 := by
    rw [ha2] at eq4
    linarith
  have hc : c = 9 := by
    rw [ha2, hb] at eq1
    linarith
  have h5 : f 5 = a * 5^2 + b * 5 + c := hf 5
  rw [h5]
  rw [ha2, hb, hc]
  norm_num
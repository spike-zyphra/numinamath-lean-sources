import Mathlib

theorem algebra_11041 (a b c : ℝ) (h : ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
    (x^3 + a * x^2 + b * x + c = 0 ∧ y^3 + a * y^2 + b * y + c = 0 ∧ z^3 + a * z^2 + b * z + c = 0) ∧
    (y - x = 1 ∧ z - y = 1)) :
    b = (a ^ 2 / 3 - 1) ∧ c = (a ^ 3 / 27 - a / 3) := by
  rcases h with ⟨x, y, z, hxne, hyne, hzne, ⟨hx, hy, hz⟩, ⟨h1, h2⟩⟩
  have eq1 : y = x + 1 := by linarith
  have eq2 : z = x + 2 := by linarith [h1, h2]
  rw [eq1] at hy 
  rw [eq2] at hz
  have eq3 : (x + 1) ^ 3 + a * (x + 1) ^ 2 + b * (x + 1) + c = 0 := hy
  have eq4 : (x + 2) ^ 3 + a * (x + 2) ^ 2 + b * (x + 2) + c = 0 := hz
  have eq5 : ((x + 1) ^ 3 + a * (x + 1) ^ 2 + b * (x + 1) + c) - (x^3 + a * x^2 + b * x + c) = 0 := by linarith [hx, eq3]
  have eq6 : (3 * x ^ 2 + 3 * x + 1) + a * (2 * x + 1) + b = 0 := by nlinarith [eq5]
  have eq7 : ((x + 2) ^ 3 + a * (x + 2) ^ 2 + b * (x + 2) + c) - ((x + 1) ^ 3 + a * (x + 1) ^ 2 + b * (x + 1) + c) = 0 := by linarith [eq3, eq4]
  have eq8 : (3 * x ^ 2 + 9 * x + 7) + a * (2 * x + 3) + b = 0 := by nlinarith [eq7]
  have eq9 : x = (-a - 3) / 3 := by 
    nlinarith [eq6, eq8]
  have eq10 : b = (a ^ 2 / 3 - 1) := by 
    rw [eq9] at eq6
    nlinarith
  have eq11 : c = (a ^ 3 / 27 - a / 3) := by 
    rw [eq9, eq10] at hx
    nlinarith
  constructor
  · exact eq10
  · exact eq11
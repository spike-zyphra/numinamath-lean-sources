import Mathlib

open Complex Function Metric Finset
open scoped BigOperators Topology

theorem algebra_1485 {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) (hb : 0 < b)
  (hord : a > b ∧ b > c) :
  max ((-(b - c) + √((b - c)^2 - 4 * (a - b) * (c - a))) / (2 * (a - b))) ((-(b - c) - √((b - c)^2 - 4 * (a - b) * (c - a))) / (2 * (a - b))) = 1 := by

  have h1 : a > b := hord.1
  have h2 : b > c := hord.2
  have h3 : a - b > 0 := by linarith
  have h4 : b - c > 0 := by linarith

  have h5 : (b - c) ^ 2 - 4 * (a - b) * (c - a) = (2 * a - (b + c)) ^ 2 := by
    nlinarith
  
  have h6 : 2 * a - (b + c) > 0 := by
    nlinarith
  
  have h7 : √((b - c) ^ 2 - 4 * (a - b) * (c - a)) = 2 * a - (b + c) := by
    rw [h5]
    rw [Real.sqrt_sq (by linarith)]
  
  have hx1 : (-(b - c) + √((b - c)^2 - 4 * (a - b) * (c - a))) / (2 * (a - b)) = 1 := by
      rw [h7]
      have h8 : -(b - c) + (2 * a - (b + c)) = 2 * (a - b) := by
          ring
      have h9 : 2 * (a - b) ≠ 0 := by
          nlinarith
      field_simp [h8, h9]
      <;> nlinarith
  
  have hx2 : (-(b - c) - √((b - c)^2 - 4 * (a - b) * (c - a))) / (2 * (a - b)) = - (a - c) / (a - b) := by
    rw [h7]
    have h8 : -(b - c) - (2 * a - (b + c)) = -2 * (a - c) := by
      ring
    have h9 : 2 * (a - b) ≠ 0 := by
      nlinarith
    field_simp [h8, h9]
    <;> nlinarith

  rw [hx1, hx2]

  have h8 : - (a - c) / (a - b) < 1 := by
    have h9 : a - b > 0 := by linarith
    have h10 : a - c > 0 := by nlinarith
    have h11 : - (a - c) < 0 := by linarith
    have h12 : - (a - c) / (a - b) < (0 : ℝ) := by
      apply div_neg_of_neg_of_pos
      linarith
      linarith
    linarith

  rw [max_eq_left (by linarith)]
  <;> nlinarith
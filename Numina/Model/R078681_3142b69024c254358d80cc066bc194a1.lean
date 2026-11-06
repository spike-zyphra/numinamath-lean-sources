import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_114798 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (p : ℝ) (hp : p = (a + b + c) / 2) :
  Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c) ≤ Real.sqrt (3 * p) := by
  have ha1 : p - a > 0 := by
    rw [hp]
    linarith
  have hb1 : p - b > 0 := by
    rw [hp]
    linarith
  have hc1 : p - c > 0 := by
    rw [hp]
    linarith
  have h1 : (Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c)) ^ 2 ≤ 3 * p := by
    nlinarith [sq_nonneg (Real.sqrt (p - a) - Real.sqrt (p - b)), sq_nonneg (Real.sqrt (p - b) - Real.sqrt (p - c)), sq_nonneg (Real.sqrt (p - a) - Real.sqrt (p - c)),
      Real.sq_sqrt (show p - a ≥ 0 by linarith), Real.sq_sqrt (show p - b ≥ 0 by linarith), Real.sq_sqrt (show p - c ≥ 0 by linarith), 
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
      hp]
  have h3 : Real.sqrt ((Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c)) ^ 2) ≤ Real.sqrt (3 * p) := by
    apply Real.sqrt_le_sqrt
    linarith [h1]
  have h4 : Real.sqrt ((Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c)) ^ 2) = Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c) := by
    have h5 : Real.sqrt ((Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c)) ^ 2) = abs (Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c)) := by 
      rw [Real.sqrt_sq_eq_abs]
    have h6 : Real.sqrt (p - a) + Real.sqrt (p - b) + Real.sqrt (p - c) ≥ 0 := by
      positivity
    rw [h5]
    rw [abs_of_nonneg h6]
  linarith [h4, h3]
import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_6385 (A B C : EuclideanSpace ℝ (Fin 2))
  (hABC : ¬Collinear ℝ {A, B, C}) (a b c : ℝ)
  (ha : dist B C = a) (hb : dist A C = b) (hc : dist A B = c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a)
  (h''' : a + b + c = 3): 3*(a^2 + b^2 + c^2) + 4*a*b*c ≥ 13 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < a + c - b by linarith),
            mul_pos (show (0 : ℝ) < a + b - c by linarith) (show (0 : ℝ) < b + c - a by linarith),
            mul_pos (show (0 : ℝ) < a + c - b by linarith) (show (0 : ℝ) < b + c - a by linarith)
          ]
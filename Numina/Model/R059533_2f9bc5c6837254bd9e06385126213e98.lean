import Mathlib.Geometry.Euclidean.Triangle
open scoped EuclideanGeometry

open scoped EuclideanGeometry

theorem inequalities_284890
  (A B C : EuclideanSpace ℝ (Fin 2))
  (a b c : ℝ)
  (h₀ : a = dist B C)
  (h₁ : b = dist A C)
  (h₂ : c = dist A B)
  (h₃ : dist B C < dist A B + dist A C)
  (h₄ : dist A C < dist A B + dist B C)
  (h₅ : dist A B < dist A C + dist B C) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by
  rw [h₀, h₁, h₂]
  nlinarith [sq_nonneg (dist B C - dist A C), sq_nonneg (dist B C - dist A B), sq_nonneg (dist A C - dist A B),
          sq_nonneg (dist B C + dist A C - dist A B), sq_nonneg (dist A C + dist A B - dist B C),
          sq_nonneg (dist B C + dist A B - dist A C),
          mul_pos (sub_pos.mpr h₃) (sub_pos.mpr h₄), mul_pos (sub_pos.mpr h₄) (sub_pos.mpr h₅), 
          mul_pos (sub_pos.mpr h₅) (sub_pos.mpr h₃)]
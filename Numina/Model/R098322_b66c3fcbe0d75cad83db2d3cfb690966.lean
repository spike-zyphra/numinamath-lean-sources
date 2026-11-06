import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem algebra_8091 {a b x y : ℝ} (h₀ : a^2 + b^2 = 2) (h₁ : x^2 + y^2 = 1003) :
    (a * x + b * y)^2 + (b * x - a * y)^2 = 2006 := by 
  have eq1 : (a * x + b * y) ^ 2 + (b * x - a * y) ^ 2 = (a^2 + b^2) * (x^2 + y^2) := by
    ring
  rw [eq1, h₀, h₁]
  all_goals norm_num
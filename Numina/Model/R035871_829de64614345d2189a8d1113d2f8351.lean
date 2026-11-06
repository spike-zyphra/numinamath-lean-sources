import Mathlib

theorem algebra_258214 (a b c x y z : ℝ) :
    (a^2 + b^2 + c^2) ∣ (a * y - b * x)^2 + (b * z - c * y)^2 + (c * x - a * z)^2 +
      (a * x + b * y + c * z)^2 ∧
    (x^2 + y^2 + z^2) ∣ (a * y - b * x)^2 + (b * z - c * y)^2 + (c * x - a * z)^2 +
      (a * x + b * y + c * z)^2 := by 
  have eq : (a * y - b * x)^2 + (b * z - c * y)^2 + (c * x - a * z)^2 +
    (a * x + b * y + c * z)^2 = (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2) := by
    ring
  constructor
  · -- Show that $a^2 + b^2 + c^2$ divides the expression.
    rw [eq]
    use x^2 + y^2 + z^2
    all_goals ring
  · -- Show that $x^2 + y^2 + z^2$ divides the expression.
    rw [eq]
    use a^2 + b^2 + c^2
    all_goals ring
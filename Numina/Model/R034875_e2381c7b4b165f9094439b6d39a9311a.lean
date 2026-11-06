import Mathlib

theorem algebra_26457 {x y z : ℝ} (h : x^2 + y = y^2 + z ∧ y^2 + z = z^2 + x) :
    x^3 + y^3 + z^3 = x * y^2 + y * z^2 + z * x^2 := by

  rcases h with ⟨h1, h2⟩

  have eq1 : x^2 = y^2 + z - y := by linarith
  have eq2 : y^2 = z^2 + x - z := by linarith
  have eq3 : z^2 = x^2 + y - x := by
    nlinarith

  have eq4 : x^3 = x * (y^2 + z - y) := by 
    calc
      x^3 = x * x^2 := by ring
      _ = x * (y^2 + z - y) := by rw [eq1]

  have eq5 : y^3 = y * (z^2 + x - z) := by 
    calc
      y^3 = y * y^2 := by ring
      _ = y * (z^2 + x - z) := by rw [eq2]

  have eq6 : z^3 = z * (x^2 + y - x) := by 
    calc
      z^3 = z * z^2 := by ring
      _ = z * (x^2 + y - x) := by rw [eq3]

  calc
    x^3 + y^3 + z^3 = x * (y^2 + z - y) + y * (z^2 + x - z) + z * (x^2 + y - x) := by 
      rw [eq4, eq5, eq6]
    _ = x * y^2 + y * z^2 + z * x^2 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
        sq_nonneg (x + y + z - (y^2 + z)), sq_nonneg (y^2 + z - (z^2 + x))
        ]
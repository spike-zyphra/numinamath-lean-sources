import Mathlib

theorem algebra_292664 {x : ℝ} (hx : x^3 + x - 1 = 0) :
    (x^4 - 2*x^3 + x^2 - 3*x + 5) / (x^5 - x^2 - x + 2) = 3 := by
  have h1 : x^3 = 1 - x := by linarith
  have h2 : x^4 = x - x^2 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (1 - x) := by rw [h1]
      _ = x - x^2 := by ring
  have h3 : x^5 = x^2 + x - 1 := by
    calc
      x^5 = x * x^4 := by ring
      _ = x * (x - x^2) := by rw [h2]
      _ = x^2 - x^3 := by ring
      _ = x^2 - (1 - x) := by rw [h1]
      _ = x^2 + x - 1 := by ring
  have num_eq : x^4 - 2 * x^3 + x^2 - 3 * x + 5 = 3 := by
    rw [h2, h1]
    linarith
  have denom_eq : x^5 - x^2 - x + 2 = 1 := by
    rw [h3]
    linarith
  rw [num_eq, denom_eq]
  all_goals norm_num
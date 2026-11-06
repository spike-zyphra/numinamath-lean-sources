import Mathlib

theorem algebra_197769 {a b c d : ℝ} (hb : b ≠ 0) (hd : d ≠ 0)
    (h1 : a + c = 2 * b) (h2 : 2 * b * d = c * (b + d)) :
    a / b = c / d := by 
  have h3 : a = 2 * b - c := by
    linarith
  have h4 : a * d = b * c := by
    rw [h3]
    have eq1 : (2 * b - c) * d = b * c := by
      have eq2 : 2 * b * d = c * (b + d) := h2
      have eq3 : c * (b + d) = c * b + c * d := by ring
      have eq4 : 2 * b * d = c * b + c * d := by linarith [eq2, eq3]
      calc 
        (2 * b - c) * d = 2 * b * d - c * d := by ring
        _ = (c * b + c * d) - c * d := by rw [show 2 * b * d = c * b + c * d by linarith [eq4]]
        _ = c * b := by ring 
        _ = b * c := by ring 
    linarith [eq1]
  field_simp [hb, hd]
  <;> linarith [h4]
import Mathlib

theorem algebra_230184 {a b c d x1 x2 : ℝ} 
    (hroots : x1^2 - (a + d) * x1 + a * d - b * c = 0 ∧ 
              x2^2 - (a + d) * x2 + a * d - b * c = 0) :
    (x1^3)^2 - (a^3 + d^3 + 3 * a * b * c + 3 * b * c * d) * (x1^3) +
    (a * d - b * c)^3 = 0 ∧ 
    (x2^3)^2 - (a^3 + d^3 + 3 * a * b * c + 3 * b * c * d) * (x2^3) +
    (a * d - b * c)^3 = 0 := by
  constructor
  · -- First part: proving the equation for x1^3
    have h1 : x1^2 = (a + d) * x1 - (a * d - b * c) := by linarith [hroots.1]
    have eq1 : (x1^3)^2 = (a + d)^3 * x1^3 - 3 * (a + d)^2 * (a * d - b * c) * x1^2 + 3 * (a + d) * (a * d - b * c)^2 * x1 - (a * d - b * c)^3 := by
      calc
        (x1^3)^2 = (x1^2)^3 := by ring
        _ = ((a + d) * x1 - (a * d - b * c))^3 := by rw [h1]
        _ = (a + d)^3 * x1^3 - 3 * (a + d)^2 * (a * d - b * c) * x1^2 + 3 * (a + d) * (a * d - b * c)^2 * x1 - (a * d - b * c)^3 := by ring
    rw [eq1]
    have eq2 : (a + d)^3 * x1^3 - 3 * (a + d)^2 * (a * d - b * c) * x1^2 + 3 * (a + d) * (a * d - b * c)^2 * x1 - (a * d - b * c)^3 - (a^3 + d^3 + 3 * a * b * c + 3 * b * c * d) * (x1^3) + (a * d - b * c)^3 = 0 := by
      have eq3 : x1^2 = (a + d) * x1 - (a * d - b * c) := h1
      have eq4 : x1^3 = ((a + d)^2 - (a * d - b * c)) * x1 - (a + d) * (a * d - b * c) := by
        calc
          x1^3 = x1 * x1^2 := by ring
          _ = x1 * ((a + d) * x1 - (a * d - b * c)) := by rw [h1]
          _ = (a + d) * x1^2 - (a * d - b * c) * x1 := by ring
          _ = (a + d) * ((a + d) * x1 - (a * d - b * c)) - (a * d - b * c) * x1 := by rw [h1]
          _ = ((a + d)^2 - (a * d - b * c)) * x1 - (a + d) * (a * d - b * c) := by ring
      rw [eq4, eq3]
      ring_nf
    linarith [eq2]
  · -- Second part: proving the equation for x2^3
    have h1 : x2^2 = (a + d) * x2 - (a * d - b * c) := by linarith [hroots.2]
    have eq1 : (x2^3)^2 = (a + d)^3 * x2^3 - 3 * (a + d)^2 * (a * d - b * c) * x2^2 + 3 * (a + d) * (a * d - b * c)^2 * x2 - (a * d - b * c)^3 := by
      calc
        (x2^3)^2 = (x2^2)^3 := by ring
        _ = ((a + d) * x2 - (a * d - b * c))^3 := by rw [h1]
        _ = (a + d)^3 * x2^3 - 3 * (a + d)^2 * (a * d - b * c) * x2^2 + 3 * (a + d) * (a * d - b * c)^2 * x2 - (a * d - b * c)^3 := by ring
    rw [eq1]
    have eq2 : (a + d)^3 * x2^3 - 3 * (a + d)^2 * (a * d - b * c) * x2^2 + 3 * (a + d) * (a * d - b * c)^2 * x2 - (a * d - b * c)^3 - (a^3 + d^3 + 3 * a * b * c + 3 * b * c * d) * (x2^3) + (a * d - b * c)^3 = 0 := by
      have eq3 : x2^2 = (a + d) * x2 - (a * d - b * c) := h1
      have eq4 : x2^3 = ((a + d)^2 - (a * d - b * c)) * x2 - (a + d) * (a * d - b * c) := by
        calc
          x2^3 = x2 * x2^2 := by ring
          _ = x2 * ((a + d) * x2 - (a * d - b * c)) := by rw [h1]
          _ = (a + d) * x2^2 - (a * d - b * c) * x2 := by ring
          _ = (a + d) * ((a + d) * x2 - (a * d - b * c)) - (a * d - b * c) * x2 := by rw [h1]
          _ = ((a + d)^2 - (a * d - b * c)) * x2 - (a + d) * (a * d - b * c) := by ring
      rw [eq4, eq3]
      ring_nf
    linarith [eq2]
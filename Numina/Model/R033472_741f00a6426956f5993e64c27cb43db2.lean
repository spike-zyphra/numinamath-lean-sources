import Mathlib

theorem algebra_1162 (m : ℚ) (c : ℕ) (p : ℚ) (h : m / 5 = p * c / 3) : (m - p*c) = m * 2/5 := by
  have eq1 : p * (c : ℚ) = (3 / 5) * m := by 
    have eq2 : m / 5 = p * (c : ℚ) / 3 := by 
      simpa using h
    linarith
  have eq3 : m - p * (c : ℚ) = m * (2 / 5) := by
    rw [show p * (c : ℚ) = (3 / 5) * m by 
      linarith [eq1]
    ]
    ring
  rw [eq3]
  <;> ring_nf
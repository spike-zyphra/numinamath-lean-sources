import Mathlib

/- A tank is to be filled with water. When the tank is one-sixth full, 130 gallons of water are added, making the tank three-fifths full. How many gallons does the tank contain when it is completely full? -/
theorem algebra_10747 (x : ℝ) (h : (1 / 6) * x + 130 = (3 / 5) * x) :
    x = 300 := by
  field_simp at h
  linarith
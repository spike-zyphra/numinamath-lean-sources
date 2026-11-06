import Mathlib

/- The length of a rectangular playground exceeds twice its width by 25 feet, and the perimeter of the playground is 650 feet. What is the area of the playground in square feet? -/
theorem algebra_15218 {l w : ℕ} (hw : l = w * 2 + 25) (hperim : 2 * (l + w) = 650) :
    l * w = 22500 := by
  have h : l + w = 325 := by linarith
  rw [hw] at h
  nlinarith
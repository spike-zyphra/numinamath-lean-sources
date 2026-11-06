import Mathlib

theorem algebra_97158 (han ian jan : ℕ) (han1 : han = ian + 1)
(han2 : han * (ian + 5) = ian * 70) (jan1 : jan = 2) (jan2 : jan * (ian + 10) = ian * 150) :
jan * (ian + 10) - ian * 150 = 150 := by
  rw [han1] at han2
  rw [jan1] at *
  omega
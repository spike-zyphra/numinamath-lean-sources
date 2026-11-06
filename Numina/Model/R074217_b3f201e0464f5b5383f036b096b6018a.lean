import Mathlib

theorem algebra_247058 {x y z : ℕ} (h : x + y + z = 150) (h1 : (1 - 2 / 7 : ℚ) * x = (1 + 2 / 7 : ℚ) * y)
    (h2 : (1 - 2 / 7 : ℚ) * y = (1 + 2 / 7 : ℚ) * z) (h3 : (1 - 2 / 7 : ℚ) * z = (1 + 2 / 7 : ℚ) * x) :
    x = 42 ∧ y = 58 ∧ z = 50 := by
  have h4 : (x : ℚ) + (y : ℚ) + (z : ℚ) = 150 := by exact_mod_cast h
  have h5 : (x : ℚ) = 0 := by
    linarith
  have h6 : (y : ℚ) = 0 := by
    linarith
  have h7 : (z : ℚ) = 0 := by
    linarith
  have h8 : (x : ℚ) + (y : ℚ) + (z : ℚ) = 0 := by
    rw [h5, h6, h7]
    norm_num
  have h9 : (x : ℚ) + (y : ℚ) + (z : ℚ) = 150 := by exact_mod_cast h
  have h10 : (0 : ℚ) = 150 := by linarith [h8, h9]
  linarith
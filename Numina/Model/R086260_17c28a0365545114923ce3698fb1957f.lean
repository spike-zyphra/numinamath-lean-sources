import Mathlib

theorem algebra_1607 {x y z : ℕ} (h₀ : (x + y) / 2 + z = 47) (h₁ : (x + z) / 2 + y = 61)
    (h₂ : (y + z) / 2 + x = 60) :
    max (max x y) z - min (min x y) z = 28 := by

  have h4 : x + y + 2 * z = 94 := by
    omega

  have h5 : x + z + 2 * y = 122 := by
    omega

  have h6 : y + z + 2 * x = 120 := by
    omega

  have h7 : x = 36 := by
    omega

  have h8 : y = 38 := by
    omega

  have h9 : z = 10 := by
    omega

  simp [h7, h8, h9]
  <;> omega
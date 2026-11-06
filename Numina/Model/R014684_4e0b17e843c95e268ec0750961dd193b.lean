import Mathlib

theorem number_theory_274700 {a b : ℤ} (h₀ : a > 0) (h₁ : b > 0)
    (h₂ : (a + 65) / (b + 5) = a / b) (h₃ : (a + 65) % (b + 5) = a % b) :
    a / b = 13 := by

  have h4 : (a + 65) = (b + 5) * ( (a + 65) / (b + 5) ) + ( (a + 65) % (b + 5) ) := by
    rw [Int.ediv_add_emod (a + 65) (b + 5)]

  have h5 : a = b * (a / b) + (a % b) := by
    rw [Int.ediv_add_emod a b]

  rw [h₂, h₃] at h4

  have h6 : a + 65 = (b + 5) * (a / b) + (a % b) := by linarith

  have h8 : 65 = 5 * (a / b) := by
    nlinarith [h5, h6]

  have h9 : a / b = 13 := by
    linarith

  exact h9
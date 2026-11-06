import Mathlib

theorem algebra_119880 {x y : ℕ} (h₀ : x * y = 540) (h₁ : (x + 5) * y = 600) :
    x = 45 ∧ y = 12 := by
  have h2 : x * y = 540 := h₀
  have h3 : (x + 5) * y = 600 := h₁

  have h4 : x * y + 5 * y = 600 := by
    linarith [h3]

  have h5 : 5 * y = 60 := by 
    linarith [h4, h2]

  have hy1 : y = 12 := by
    omega

  have hx1 : x = 45 := by
    rw [hy1] at h2
    omega

  exact ⟨hx1, hy1⟩
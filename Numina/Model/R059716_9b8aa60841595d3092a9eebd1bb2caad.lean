import Mathlib

theorem algebra_269983 {x y : ℕ} (h : x ≥ 4) (h1 : x - 4 = 2 * (y + 4)) (h2 : x + 2 = 11 * (y - 2)) :
    x = 20 ∧ y = 4 := by 
  have h3 : x = 2 * y + 12 := by
    omega
  have h4 : y = 4 := by 
    omega
  have h5 : x = 20 := by 
    rw [h4] at h3
    omega
  exact ⟨h5, h4⟩
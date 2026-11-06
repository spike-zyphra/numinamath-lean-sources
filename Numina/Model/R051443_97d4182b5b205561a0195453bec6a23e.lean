import Mathlib

theorem algebra_108321 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x + 4 * y = 16) (h2 : x + 6 * y = 22) :
    y = 3 ∧ x = 4 := by
  have hy' : y = 3 := by 
    linarith
  have hx' : x = 4 := by
    rw [hy'] at h1
    linarith
  exact ⟨hy', hx'⟩
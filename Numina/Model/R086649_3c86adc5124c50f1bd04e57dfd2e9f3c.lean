import Mathlib

theorem algebra_235173 {x y : ℤ} (h : x * y = x + y) (h' : x * y = x - y) :
    x = 0 ∧ y = 0 := by
  have eq1 : x + y = x - y := by
    linarith
  have hy : y = 0 := by 
    linarith
  have hx : x = 0 := by
    rw [hy] at h
    linarith 
  exact ⟨hx, hy⟩
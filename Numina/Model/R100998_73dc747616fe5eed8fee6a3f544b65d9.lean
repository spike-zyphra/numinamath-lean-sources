import Mathlib

theorem algebra_14276 {x y t : ℤ} (hxy : x = 2 - t ∧ y = 4 * t + 7) (ht : x = -3) : y = 27 := by
  rcases hxy with ⟨hx, hy⟩
  have ht_val : t = 5 := by 
    linarith [hx, ht]
  rw [ht_val] at hy
  linarith
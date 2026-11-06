import Mathlib

theorem algebra_95281
  {f : ℝ → ℝ}
  (h : ∀ x y, 0 < x → 0 < y → f (x * y) = f x / y)
  (h' : f 500 = 3) :
  f 600 = 5 / 2 := by

  calc
    f 600 = f (500 * (6/5)) := by ring
        _ = f 500 / (6/5) :=  by rw [h 500 (6/5) (by linarith) (by linarith)]
        _ = 3 / (6/5) := by rw [h']
        _ = 5/2 := by ring
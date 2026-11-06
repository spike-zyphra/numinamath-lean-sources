import Mathlib

theorem number_theory_188915 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h : x * 4 + y * 2 = 888) (h' : x = y + 8) :
    y = 170 := by 
        rw [h'] at h 
        omega
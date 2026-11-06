import Mathlib

theorem algebra_167551 {f : ℤ → ℤ} (h : ∀ x y, f x + f y = f (x + 1) + f (y - 1)) (h2016 : f 2016 = 6102) (h6102 : f 6102 = 2016) : f 1 = 8117 := by

  -- Prove the function is linear
  -- For any integer y, f(y) = f(0) + y*(f(1) - f(0))
  have f_linear : ∀ y : ℤ, f y = f 0 + y * (f 1 - f 0) := by 
    intro y
    induction y using Int.induction_on with
    | hz =>
      simp
    | hp i hi =>
      specialize h 0 (i + 1)
      simp at h
      have eq1 : f (i + 1) = f i + (f 1 - f 0) := by 
        omega
      rw [eq1]
      rw [hi]
      ring
    | hn i hi =>
      specialize h 0 (-i)
      simp at h 
      have eq2 : f (-i - 1) = f (-i) - (f 1 - f 0) := by 
        omega
      rw [eq2]
      rw [hi]
      ring

  have eq1 := f_linear 2016 
  have eq2 := f_linear 6102
  simp at eq1 eq2
  rw [h2016] at eq1 
  rw [h6102] at eq2 
  omega
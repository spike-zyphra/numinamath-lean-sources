import Mathlib

theorem algebra_71497 {p q : ℤ} (f : ℤ → ℤ) (hf : ∀ x, f x = x ^ 2 + p * x + q) :
    ∃ m, f m = f 2015 * f 2016 := by

  use 2015 + (2015 ^ 2 + p * 2015 + q)

  have eq2015 : f 2015 = 2015 ^ 2 + p * 2015 + q := by 
    apply hf

  have eq2016 : f 2016 = 2016 ^ 2 + p * 2016 + q := by 
    apply hf

  simp [eq2015, eq2016, hf]
  <;> ring
import Mathlib

theorem algebra_128585 (x y k : ℤ) (h₀ : 3 * x + 5 * y = k ^ 2) (h₁ : x + y = 7 * k) :
    x = k * (35 - k) / 2 ∧ y = k * (k - 21) / 2 := by

  have eq1 : 2 * x = k * (35 - k) := by
    have eq2 : y = 7 * k - x := by
      omega
    rw [eq2] at h₀
    linarith

  have eq2 : 2 * y = k * (k - 21) := by
    have eq3 : y = 7 * k - x := by
      omega
    have eq4 : 2 * y = k * (k - 21) := by
      calc
        2 * y = 2 * (7 * k - x) := by 
          rw [eq3]
        _ = 14 * k - 2 * x := by 
          ring
        _ = 14 * k - k * (35 - k) := by 
          rw [show 2 * x = k * (35 - k) by linarith [eq1] ]
        _ = k * (k - 21) := by 
          ring
    exact_mod_cast eq4

  constructor
  · -- x = k * (35 - k) / 2
    have hx : 2 * x = k * (35 - k) := eq1
    have : x = k * (35 - k) / 2 := by 
      omega
    exact_mod_cast this

  · -- y = k * (k - 21) / 2
    have hy : 2 * y = k * (k - 21) := eq2
    have : y = k * (k - 21) / 2 := by 
      omega
    exact_mod_cast this
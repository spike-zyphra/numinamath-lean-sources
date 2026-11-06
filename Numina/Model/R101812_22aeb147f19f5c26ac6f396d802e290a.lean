import Mathlib

theorem algebra_150568 (a d : ℤ) (h₀ : a = 9) (h₁ : a + 7 * d = 12) :
    {n | n ∈ Finset.range 2015 ∧ 3 ∣ a + n * d}.ncard = 288 := by 
  rw [h₀] at h₁ 
  omega
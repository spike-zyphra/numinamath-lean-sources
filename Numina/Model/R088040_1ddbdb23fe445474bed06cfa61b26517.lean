import Mathlib

theorem algebra_19866 {a b c : ℤ} (h₀ : a + b = c) (h₁ : b + c = 11) (h₂ : c = 8) :
    a = 5 := by 
  have hb : b = 3 := by
    rw [h₂] at h₁ -- Substitute c = 8 into b + c = 11
    linarith -- Solving b + 8 = 11 gives b = 3
  rw [hb, h₂] at h₀ -- Substitute b = 3 and c = 8 into a + b = c
  linarith -- Solving a + 3 = 8 gives a = 5
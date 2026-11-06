import Mathlib

theorem algebra_203979 (walk bike moped : ℝ)
    (h₀ : 0 < walk ∧ 0 < bike ∧ 0 < moped)
    (h₁ : walk = 5)
    (h₂ : bike = 4 * walk)
    (h₃ : moped = 3 * bike) :
    moped - bike = 40 := by 
  rw [h₁] at h₂ 
  have hbike : bike = 20 := by 
    linarith
  rw [hbike] at h₃
  have hmoped : moped = 60 := by 
    linarith
  rw [hmoped, hbike]
  all_goals linarith
import Mathlib

theorem algebra_15871 (r b g : ℕ)
    (h₀ : r * 5 = b * 1) (h₁ : g * 1 = r * 3) (h₂ : g = 27) :
    r + b + g = 81 := by
  have hb : b = 5 * r := by
    omega
  have hg : g = 3 * r := by
    omega
  have hr : r = 9 := by
    rw [hg] at h₂
    omega
  have hb9 : b = 45 := by
    rw [hr] at hb
    omega
  calc
    r + b + g = 9 + 45 + 27 := by rw [hr, hb9, h₂]
    _ = 81 := by norm_num
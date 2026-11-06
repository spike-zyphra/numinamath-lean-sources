import Mathlib

theorem algebra_196235 (c s : ℝ) (h₀ : c + s = 2500) (h₁ : 4*c+3*s=8870) :
    c=1370 ∧ s=1130 := by
  have hs : s = 2500 - c := by linarith
  rw [hs] at h₁
  have hc : c = 1370 := by linarith
  have hs2 : s = 1130 := by
    rw [hc] at hs
    linarith
  exact ⟨hc, hs2⟩
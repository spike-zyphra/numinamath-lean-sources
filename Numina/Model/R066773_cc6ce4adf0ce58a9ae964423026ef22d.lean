import Mathlib

theorem algebra_281455 (misha kolya vitya : ℝ)
    (h₀ : misha = kolya + 943) (h₁ : vitya = misha + 127) (h₂ : misha + kolya = vitya + 479) :
    misha = 1549 ∧ kolya = 606 ∧ vitya = 1676 := by
  have hkolya : kolya = 606 := by
    rw [h₁, h₀] at h₂
    linarith
  have hmisha : misha = 1549 := by
    rw [hkolya] at h₀
    linarith
  have hvitya : vitya = 1676 := by
    rw [hmisha] at h₁
    linarith
  exact ⟨hmisha, hkolya, hvitya⟩
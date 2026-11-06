import Mathlib

theorem algebra_208707 (a : Fin 13 → Fin 13 → ℝ)
    (h₀ : ∀ i j, a i j = a 0 0 + i * (a 0 1 - a 0 0) + j * (a 1 0 - a 0 0))
    (h₁ : a 0 0 = 1) (h₂ : a 0 1 = 2) (h₃ : a 1 0 = 3) (h₄ : a 1 1 = 6) :
    ∑ i, ∑ j, (if (i + j) % 2 = 0 then 0 else a i j) = 252 := by 
  have h5 : a 0 1 = a 0 0 + (0 : Fin 13) * (a 0 1 - a 0 0) + (1 : Fin 13) * (a 1 0 - a 0 0) := by
    specialize h₀ 0 1
    simpa using h₀

  simp [h₁, h₃] at h5 
  linarith [h₂, h5]
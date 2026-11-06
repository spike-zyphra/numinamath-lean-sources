import Mathlib

theorem algebra_10461 (x1 x2 y1 y2 : ℝ) (h : (x1, y1) = (2, 5) ∧ (x2, y2) = (-6, -1)) :
    Real.sqrt ((x2 - x1)^2 + (y2 - y1)^2) = 10 := by 
  rcases h with ⟨h₁, h₂⟩ 
  simp [Prod.mk.injEq] at h₁ h₂ 
  rcases h₁ with ⟨rfl, rfl⟩
  rcases h₂ with ⟨rfl, rfl⟩
  have : Real.sqrt ((-6 - 2: ℝ)^2 + (-1 - 5)^2) = Real.sqrt (100 : ℝ) := by norm_num
  rw [this]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
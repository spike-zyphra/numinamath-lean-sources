import Mathlib

theorem algebra_322665 {a b c : ℝ} (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (h₁ : a * x₁^2 + b * x₁ + c = 0) (h₂ : a * x₂^2 + b * x₂ + c = 0)
    (s₁ s₂ s₃ : ℝ) (hs₁ : s₁ = x₁ + x₂) (hs₂ : s₂ = x₁^2 + x₂^2)
    (hs₃ : s₃ = x₁^3 + x₂^3) :
    a * s₃ + b * s₂ + c * s₁ = 0 := by
  rw [hs₁, hs₂, hs₃]
  have eq₁ : a * x₁^3 + b * x₁^2 + c * x₁ = 0 := by
    have eq₁ : a * x₁^2 + b * x₁ + c = 0 := h₁
    -- Multiply by x₁
    calc
      a * x₁^3 + b * x₁^2 + c * x₁ = x₁ * (a * x₁^2 + b * x₁ + c) := by ring_nf
      _ = x₁ * 0 := by rw [eq₁]
      _ = 0 := by simp
  have eq₂ : a * x₂^3 + b * x₂^2 + c * x₂ = 0 := by
    have eq₂ : a * x₂^2 + b * x₂ + c = 0 := h₂
    -- Multiply by x₂
    calc
      a * x₂^3 + b * x₂^2 + c * x₂ = x₂ * (a * x₂^2 + b * x₂ + c) := by ring_nf
      _ = x₂ * 0 := by rw [eq₂]
      _ = 0 := by simp
  -- Now sum eq₁ and eq₂
  have eq₃ : a * (x₁^3 + x₂^3) + b * (x₁^2 + x₂^2) + c * (x₁ + x₂) = 0 := by
    linarith [eq₁, eq₂]
  -- The statement is precisely eq₃
  linarith [eq₃]
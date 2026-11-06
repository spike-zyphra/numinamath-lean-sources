import Mathlib

theorem algebra_326901 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x) (x₁ x₂ : ℝ)
    (hx₁ : f x₁ = f x₂) (hx₂ : x₁ ≠ x₂) :
    f (x₁ + x₂) = 0 := by

  have eq₁ : a * x₁ ^ 2 + b * x₁ = a * x₂ ^ 2 + b * x₂ := by
    rw [hf] at hx₁
    simp at hx₁
    linarith

  have eq₂ : a * (x₁ ^ 2 - x₂ ^ 2) + b * (x₁ - x₂) = 0 := by
    linarith [eq₁]

  have eq₃ : (x₁ - x₂) * (a * (x₁ + x₂) + b) = 0 := by
    have h1 : x₁ ^ 2 - x₂ ^ 2 = (x₁ - x₂) * (x₁ + x₂) := by
      ring
    rw [h1] at eq₂
    linarith

  cases' (mul_eq_zero.mp eq₃) with h4 h5
  · -- Case $x₁ - x₂ = 0$
    exfalso
    apply hx₂
    linarith
  · -- Case $a * (x₁ + x₂) + b = 0$
    have h6 : a * (x₁ + x₂) + b = 0 := by
      linarith [h5]
    have eq₄ : f (x₁ + x₂) = a * (x₁ + x₂) ^ 2 + b * (x₁ + x₂) := by
      rw [hf]
    rw [eq₄]
    have h7 : a * (x₁ + x₂) ^ 2 + b * (x₁ + x₂) = (a * (x₁ + x₂) + b) * (x₁ + x₂) := by
      ring
    rw [h7, h6]
    all_goals norm_num
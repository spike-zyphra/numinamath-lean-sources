import Mathlib

theorem algebra_185730 {x y z : ℝ} (h₀ : ∃ q : ℚ, x + y * z = q)
    (h₁ : ∃ q : ℚ, y + z * x = q) (h₂ : ∃ q : ℚ, z + x * y = q)
    (h₃ : x ^ 2 + y ^ 2 = 1) : ∃ q : ℚ, x * y * z ^ 2 = q := by
  rcases h₀ with ⟨q₀, h₀⟩
  rcases h₁ with ⟨q₁, h₁⟩
  rcases h₂ with ⟨q₂, h₂⟩
  have h4 : (x + y * z) * (y + z * x) = (q₀ : ℝ) * (q₁ : ℝ) := by
    rw [h₀, h₁]
    all_goals norm_num
  have eq1 : (x + y * z) * (y + z * x) = x * y + (x ^ 2 + y ^ 2) * z + x * y * z ^ 2 := by
    ring
  rw [eq1] at h4
  rw [h₃] at h4
  have h5 : x * y * z ^ 2 = (q₀ : ℝ) * (q₁ : ℝ) - (q₂ : ℝ) := by
    have h6 : (z + x * y) = (q₂ : ℝ) := by linarith [h₂]
    nlinarith [h6]
  use (q₀ * q₁ - q₂)
  simp [h5]
  all_goals norm_num
  all_goals linarith
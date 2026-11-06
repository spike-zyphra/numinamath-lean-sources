import Mathlib

theorem algebra_134412 (s : ℝ → ℝ) (v : ℝ → ℝ) (T : ℝ → ℝ)
    (h₀ : s 1 = 75 * 1) (h₁ : ∀ t ∈ Set.Icc 1 1.5, T t = (300 - s t) / (v t))
    (h₂ : v 1 = 75) (h₃ : ∀ t ∈ Set.Icc 1 1.5, v t = (s t - s 1) / (t - 1)) :
    s 90 / 60 = 180 := by 
  have h₄ : v 1 = (s 1 - s 1) / (1 - 1) := by
    specialize h₃ 1 (by norm_num [Set.mem_Icc])
    simpa using h₃
  -- We know from hypothesis h₀ that s 1 = 75.
  have h₅ : s 1 - s 1 = (0 : ℝ) := by
    linarith
  -- Compute (1 - 1).
  have h₆ : (1 - 1 : ℝ) = (0 : ℝ) := by
    norm_num
  -- Substitute these values into h₄.
  have h₇ : v 1 = (0 : ℝ) / (0 : ℝ) := by
    rw [h₄]
    rw [h₅, h₆]
  -- In Lean's standard library, division by zero equals zero.
  have h₈ : v 1 = (0 : ℝ) := by
    rw [h₇]
    simp [div_zero]
  -- This contradicts hypothesis h₂: v 1 = 75.
  linarith [h₂, h₈]
import Mathlib

theorem algebra_277873 (f : ℝ → ℝ) (h₀ : ∀ x, f (x + 2) = f x) (h₁ : ∀ x, f (-x) = f x)
    (h₂ : ∀ x ∈ Set.Icc 2 3, f x = x) :
    ∀ x ∈ Set.Icc (-2) 0, f x = 3 - abs (x + 1) := by
  intro x hx
  have h3 : -2 ≤ x := hx.1
  have h4 : x ≤ 0 := hx.2
  by_cases h5 : x ≥ -1
  · -- Case $x \geq -1$ (so $x \in [-1, 0]$)
    have h6 : -1 ≤ x := h5
    have h7 : x ≤ 0 := h4
    have h8 : -x ≥ 0 := by linarith
    have h9 : -x ≤ 1 := by linarith
    have h10 : -x ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    -- Compute f(-x) for -x ∈ [0, 1]
    have hfx1 : f (-x) = -x + 2 := by
      have h13 : f (-x + 2) = (-x) + 2 := by
        have h14 : (-x + 2) ∈ Set.Icc (2 : ℝ) 3 := by
          constructor <;> nlinarith
        specialize h₂ (-x + 2) h14
        simpa using h₂
      have h14 : f (-x + 2) = f (-x) := by
        specialize h₀ (-x)
        simpa using h₀
      linarith [h13, h14]
    -- Compute f(x) using f(x) = f(-x)
    have hfx2 : f x = 2 - x := by
      have h15 : f x = f (-x) := by
        have h16 : f (-x) = f x := by
          specialize h₁ x
          simpa using h₁
        linarith [h16]
      linarith [hfx1, h15]
    have h18 : abs (x + 1) = x + 1 := by
      rw [abs_of_nonneg]
      linarith
    rw [h18]
    all_goals linarith [hfx2]
  · -- Case $x < -1$ (so $x \in [-2, -1]$)
    have h6 : x < -1 := by linarith
    have h7 : -2 ≤ x := h3
    have h8 : x < -1 := h6
    -- Compute f(x) for x ∈ [-2, -1)
    have h9 : x + 2 ≥ 0 := by linarith
    have h10 : x + 2 < 1 := by linarith
    have h11 : x + 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    -- Compute f(x + 2) for x + 2 ∈ [0, 1)
    have hfx3 : f (x + 2) = (x + 2) + 2 := by
      have h13 : f (x + 2 + 2) = (x + 2) + 2 := by
        have h14 : (x + 2 + 2) ∈ Set.Icc (2 : ℝ) 3 := by
          constructor <;> nlinarith
        specialize h₂ (x + 2 + 2) h14
        simpa using h₂
      have h14 : f (x + 2 + 2) = f (x + 2) := by
        specialize h₀ (x + 2)
        simpa using h₀
      linarith [h13, h14]
    -- Compute f(x) using periodicity
    have hfx4 : f x = x + 4 := by
      have h15 : f x = f (x + 2) := by
        have h16 : f (x + 2) = f x := by
          specialize h₀ x
          simpa using h₀
        linarith [h16]
      linarith [hfx3, h15]
    -- Check the final expression
    have h13 : abs (x + 1) = -(x + 1) := by
      rw [abs_of_nonpos]
      · linarith
      all_goals linarith
    rw [h13]
    all_goals linarith [hfx4]
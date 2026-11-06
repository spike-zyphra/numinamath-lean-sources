import Mathlib

theorem algebra_111660 (f : ℝ → ℝ) :
    (∀ x, f (f x * f (1 - x)) = f x) ∧ (∀ x, f (f x) = 1 - f x) ↔
    ∀ x, f x = 1 / 2 := by
  constructor
  · -- Assume both conditions hold, prove that f(x) = 1/2 for all x
    rintro ⟨h1, h2⟩
    -- Prove that f(x) = f(1 - f(x))
    have h3 : ∀ x, f x = f (1 - f x) := by
      intro x
      have eq1 := h2 (f x)
      have eq2 := h2 x
      have eq3 : f (f (f x)) = f x := by
        linarith [eq1, eq2]
      have eq7 : f (f (f x)) = f (1 - f x) := by
        rw [h2 x]
      linarith [eq3, eq7]
    -- Prove that f(x) = f(1 - x)
    have h4 : ∀ x, f x = f (1 - x) := by
      intro x
      have eq1 := h1 x
      have eq2 := h1 (1 - x)
      have eq3 : 1 - (1 - x : ℝ) = x := by ring
      rw [eq3] at eq2
      have eq5 : f (f x * f (1 - x)) = f (f (1 - x) * f x) := by
        have eq6 : f x * f (1 - x) = f (1 - x) * f x := by ring
        rw [eq6]
      have eq7 := eq1
      have eq8 := eq2
      -- One side of the equation
      linarith [eq1, eq2, eq5]
    -- Solve equations to find f(x) = 1/2
    have h5 : ∀ x, f x = 1 / 2 := by
      intro x
      have eq1 := h2 x
      have eq2 := h4 x
      have eq3 := h4 (f x)
      have eq4 : f (1 - f x) = 1 - f x := by
        have : f (1 - f x) = 1 - f x := by
          have ht1 : f (f x) = 1 - f x := h2 x
          have ht2 : f (f x) = f (1 - f x) := by
            apply h4 (f x)
          linarith [ht1, ht2]
        linarith [this]
      have eq5 : f x = 1 - f x := by
        have eq6 : f x = f (1 - f x) := by
          apply h3 x
        rw [eq6]
        linarith [eq4]
      linarith [eq5]
    exact h5
  · -- Assume f(x) = 1/2 for all x, prove both conditions
    intro hf
    constructor
    · -- First condition
      intro x
      have hx1 : f x = 1 / 2 := by
        apply hf x
      have hx2 : f (1 - x) = 1 / 2 := by
        apply hf (1 - x)
      have : (f x * f (1 - x)) = (1 / 4 : ℝ) := by
        rw [hx1, hx2]
        ring
      rw [this]
      have h4 : f (1 / 4 : ℝ) = 1 / 2 := by
        apply hf (1 / 4 : ℝ)
      rw [h4]
      linarith [hx1]
    · -- Second condition
      intro x
      have hx1 : f x = 1 / 2 := by
        apply hf x
      have hx2 : f (f x) = 1 / 2 := by
        rw [hx1]
        apply hf (1 / 2 : ℝ)
      have hx3 : 1 - f x = 1 / 2 := by
        linarith [hx1]
      linarith [hx2, hx3]
import Mathlib

theorem algebra_122584 {f g : ℝ → ℝ} (hf : StrictMono f)
    (hg : StrictMono g) (hfg : Function.LeftInverse g f) (hinv : Function.RightInverse g f)
    (x₁ x₂ : ℝ) (hx₁ : f x₁ + x₁ = 2) (hx₂ : g x₂ + x₂ = 2) :
    x₁ + x₂ = 2 := by 
  have eq1 : f x₁ = 2 - x₁ := by 
    linarith
  have eq2 : f (2 - x₂) = x₂ := by
    have h1 : g x₂ = 2 - x₂ := by
      linarith
    have h2 : f (g x₂) = x₂ := by
      apply hinv
    rw [h1] at h2
    linarith
  have eq3 : x₁ = 2 - x₂ := by 
    by_cases h : x₁ < 2 - x₂
    · -- Assume x₁ < 2 - x₂
      have h1 : f x₁ < f (2 - x₂) := by
        apply hf.lt_iff_lt.2
        linarith
      have h2 : 2 - x₁ < x₂ := by
        nlinarith [eq1, eq2, h1]
      nlinarith 
    by_cases h2 : x₁ > 2 - x₂
    · -- Assume x₁ > 2 - x₂
      have h3 : f x₁ > f (2 - x₂) := by
        apply hf.lt_iff_lt.2
        linarith
      have h4 : 2 - x₁ > x₂ := by
        nlinarith [eq1, eq2, h3]
      nlinarith 
    linarith 
  nlinarith [eq3]
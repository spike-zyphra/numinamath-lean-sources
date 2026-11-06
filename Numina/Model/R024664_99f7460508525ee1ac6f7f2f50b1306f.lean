import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_218839 {f g : ℝ → ℝ}
  (hf : ∀ x, x ≥ 0 → f x = x)
  (hf' : ∀ x, x < 0 → f x = 0)
  (hg : ∀ x, x < 2 → g x = 2 - x)
  (hg' : ∀ x, x ≥ 2 → g x = 0) :
  ∀ x, f (g x) > g (f x) ↔ x < 0 := by
  intro x 
  constructor 
  · -- Assume f(g(x)) > g(f(x)), prove x < 0 
    intro h
    by_cases h1 : x < (0 : ℝ)
    · -- Assume x < 0
      have hfx : f x = 0 := hf' x h1 
      have hgx : g x = 2 - x := by 
        apply hg
        linarith
      have h11 : f (g x) = 2 - x := by 
        rw [hgx]
        have h11 : (2 - x : ℝ) ≥ 0 := by linarith 
        rw [hf (2 - x) h11]
      have h22 : g (f x) = 2 := by 
        rw [hfx]
        norm_num [hg]
      linarith [h, h11, h22]
      all_goals linarith 
    · -- Assume x ≥ 0 
      have h11 : x ≥ 0 := by linarith 
      by_cases h2 : x < (2 : ℝ)
      · -- Assume 0 ≤ x < 2 
        have hgx : g x = 2 - x := by 
          apply hg
          linarith
        have hfx : f x = x := hf x (by linarith)
        have h11 : f (g x) = 2 - x := by
          rw [hgx]
          have h11 : (2 - x : ℝ) ≥ 0 := by linarith 
          rw [hf (2 - x) h11]
        have h3' : g (f x) = (2 - x : ℝ) := by
          have h3' : g x = (2 - x : ℝ) := by
            have h5 : x < (2 : ℝ) := by linarith
            specialize hg x h5
            simpa using hg 
          rw [hfx]
          linarith [h3']
        linarith [h, h11, h3']
      · -- Assume x ≥ 2 
        have h22 : x ≥ (2 : ℝ) := by linarith 
        have hgx : g x = (0 : ℝ) := by 
          apply hg' 
          all_goals linarith 
        have hfx : f x = x := hf x (by linarith)
        have h11 : f (g x) = (0 : ℝ) := by 
          rw [hgx]
          specialize hf (0 : ℝ) (by norm_num)
          rw [hf]
        have h3' : g (f x) = (0 : ℝ) := by
          rw [hfx]
          specialize hg' x (by linarith)
          rw [hg']
        linarith [h, h11, h3']
  · -- Assume x < 0, prove f(g(x)) > g(f(x))
    intro h 
    have h1 : x < 0 := h 
    have hfx : f x = (0 : ℝ) := hf' x h1 
    have hgx : g x = (2 - x : ℝ) := by 
      apply hg 
      linarith 
    have h11 : f (g x) = (2 - x : ℝ) := by 
      rw [hgx]
      have h11 : (2 - x : ℝ) ≥ 0 := by linarith 
      rw [hf (2 - x) h11]
    have h22 : g (f x) = (2 : ℝ) := by 
      rw [hfx]
      norm_num [hg]
    linarith [h11, h22, h1]
import Mathlib

open Set Real

theorem algebra_98507 {f g : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 2, f x ∈ Icc 0 1)
    (hg : g = fun x => 1 - f (x + 1)) : ∀ x ∈ Icc (-1) 1, g x ∈ Icc 0 1 := by 
  intro x hx
  have h1 : x ≥ -1 := by
    have h1 : x ∈ Icc (-1 : ℝ) 1 := hx
    exact h1.1
  have h2 : x ≤ 1 := by
    have h1 : x ∈ Icc (-1 : ℝ) 1 := hx
    exact h1.2
  have h3 : x + 1 ≥ 0 := by linarith
  have h4 : x + 1 ≤ 2 := by linarith
  have h5 : f (x + 1) ∈ Icc (0 : ℝ) 1 := by
    apply hf
    constructor
    · -- Show x + 1 ∈ Icc 0 2 
      linarith 
    · -- Show x + 1 ∈ Icc 0 2 
      linarith 
  rw [hg]
  simp only [mem_Icc] at h5 ⊢
  -- h5 is the hypothesis 0 ≤ f (x + 1) ∧ f (x + 1) ≤ 1
  -- Goal is to show 0 ≤ 1 - f (x + 1) ∧ 1 - f (x + 1) ≤ 1
  constructor
  · -- Show 0 ≤ 1 - f (x + 1)
    linarith [h5.2]
  · -- Show 1 - f (x + 1) ≤ 1
    linarith [h5.1]
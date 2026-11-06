import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_607735 {f : ℝ → ℝ}
  (h : ∀ x y, f (x + y) * f (x - y) ≥ f x ^ 2 - f y ^ 2)
  (h' : ∃ x₀ y₀, f (x₀ + y₀) * f (x₀ - y₀) > f x₀ ^ 2 - f y₀ ^ 2) :
    (∀ x, f x ≥ 0) ∨ (∀ x, f x ≤ 0) := by
  have crux : ∀ s t, f s * (f t + f (-t)) ≥ 0 := by
    intro s t
    have := h ((s + t) / 2) ((s - t) / 2)
    have h1 : f s * f t ≥ f ((s + t) / 2) ^ 2 - f ((s - t) / 2) ^ 2 := by 
      linear_combination (norm := ring_nf) this
      rfl
    have := h ((s - t) / 2) ((s + t) / 2)
    have h2 : f s * f (-t) ≥ f ((s - t) / 2) ^ 2 - f ((s + t) / 2) ^ 2 := by
      linear_combination (norm := ring_nf) this
      rfl
    linear_combination (norm := ring_nf) h1 + h2
    rfl
  obtain ⟨x₀, y₀, hxy₀⟩ := h'
  have h6 : f (x₀ + y₀) * (f (x₀ - y₀) + f (-(x₀ - y₀))) > 0 := by
    let s := x₀ + y₀
    let t := x₀ - y₀
    have h2 := h ((s - t) / 2) ((s + t) / 2)
    linear_combination (norm := ring_nf) h2 + hxy₀
    rfl
  set t₀ := x₀ - y₀ with ht₀
  have h7 : f t₀ + f (-t₀) ≠ 0 := by
    have h7 : f (x₀ + y₀) * (f t₀ + f (-t₀)) > 0 := by
      rw [show -(x₀ - y₀) = -t₀ by simp [ht₀]] at h6
      linarith
    by_contra h_eq
    rw [h_eq] at h7
    nlinarith
  by_cases h8 : f t₀ + f (-t₀) > 0
  · -- Assume $f t₀ + f (-t₀) > 0$, prove $\forall x, f x \geq 0$
    left
    intro s
    have h9 : f s * (f t₀ + f (-t₀)) ≥ 0 := by 
      apply crux s t₀
    have h10 : f s ≥ 0 := by 
      nlinarith 
    exact h10
  · -- Assume not $f t₀ + f (-t₀) > 0$ 
    have h8' : f t₀ + f (-t₀) < 0 := by 
      by_contra h
      push_neg at h
      have : f t₀ + f (-t₀) = 0 := by linarith 
      contradiction
    right
    intro s
    have h9 : f s * (f t₀ + f (-t₀)) ≥ 0 := by 
      apply crux s t₀
    have h10 : f s ≤ 0 := by 
      nlinarith 
    exact h10
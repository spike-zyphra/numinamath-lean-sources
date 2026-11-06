import Mathlib

open BigOperators Complex Filter Finset Real TopologicalSpace Topology

theorem calculus_64385 (f : ℝ → ℝ) :
    (∀ x, 0 ≤ f x) ∧
    (∀ x, DifferentiableAt ℝ f x) ∧
    (∀ x, 0 ≤ deriv f x) ∧
    (∀ n : ℤ, f n = 0) ↔ ∀ x, f x = 0 := by
  constructor
  · -- Assume the four conditions hold, prove f(x) = 0 for all x.
    intro h
    rcases h with ⟨h1, h2, h3, h4⟩
    have h5 : Monotone f := by
      apply monotone_of_deriv_nonneg
      · -- Show f is differentiable everywhere
        intro x
        exact h2 x
      · -- Show the derivative is non-negative everywhere
        intro x
        exact h3 x
    intro x
    have hx1 := h4 (⌊x⌋)
    have hx2 := h4 (⌈x⌉)
    have h6 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h7 : x ≤ (⌈x⌉ : ℝ) := by exact Int.le_ceil x
    have h8 : f (⌊x⌋ : ℝ) ≤ f x := by
      apply h5
      linarith
    have h9 : f x ≤ f (⌈x⌉ : ℝ) := by
      apply h5
      linarith
    have h10 : f (⌊x⌋ : ℝ) = 0 := by
      simpa using hx1
    have h11 : f (⌈x⌉ : ℝ) = 0 := by
      simpa using hx2
    have h12 : f x = 0 := by
      linarith
    exact h12
  · -- Assume f(x) = 0 for all x, prove the four conditions.
    intro h
    constructor
    · -- Show non-negativity
      intro x
      have h1 : f x = 0 := h x
      linarith
    constructor
    · -- Show differentiability
      intro x
      have hf1 : f = fun (y : ℝ) => (0 : ℝ) := by
        funext y
        apply h
      rw [hf1]
      simp
    constructor
    · -- Show non-negative derivatives
      intro x
      have hf1 : f = fun (y : ℝ) => (0 : ℝ) := by
        funext y
        apply h
      rw [hf1]
      simp
    · -- Show f n = 0
      intro n
      have h1 : f (n : ℝ) = 0 := h (n : ℝ)
      simpa using h1
import Mathlib

theorem algebra_166021 {f g : ℝ → ℝ} (hf : StrictMono f) :
    (∀ x, f (g (x + 2017)) ≥ f x ∧ f x ≥ f (g x + 2017)) ↔
    g = fun x => x - 2017 := by
  constructor
  · -- Assume ∀ x, f (g (x + 2017)) ≥ f x ∧ f x ≥ f (g x + 2017), prove g = fun x => x - 2017
    intro h
    have h1 : ∀ x, f (g (x + 2017)) ≥ f x := by
      intro x
      have h1 := (h x).1
      simpa using h1
    have h2 : ∀ x, f x ≥ f (g x + 2017) := by
      intro x
      have h2 := (h x).2
      simpa using h2
    have h3 : ∀ x, g (x + 2017) ≥ x := by
      intro x
      have h1' := h1 x
      by_contra h'
      push_neg at h'
      have h4 : f (g (x + 2017)) < f x := by
        apply hf.lt_iff_lt.mpr
        linarith
      linarith
    have h4 : ∀ x, x ≥ g x + 2017 := by
      intro x
      have h2' := h2 x
      by_contra h'
      push_neg at h'
      have h5 : f x < f (g x + 2017) := by
        apply hf.lt_iff_lt.mpr
        linarith
      linarith
    funext x
    have eq1 := h3 (x - 2017)
    simp at eq1 ⊢
    have eq2 : g x ≤ x - 2017 := by
      have h5 := h4 x
      linarith
    have eq3 : g x ≥ x - 2017 := by
      have h6 := h3 (x - 2017)
      simp at h6 ⊢
      linarith
    linarith
  · -- Assume g = fun x => x - 2017, prove ∀ x, f (g (x + 2017)) ≥ f x ∧ f x ≥ f (g x + 2017)
    intro h_eq
    intro x
    have h1 : g (x + 2017) = x := by
      rw [h_eq]
      simp
      <;> ring
    have h2 : g x + 2017 = x := by
      rw [h_eq]
      simp
      <;> ring
    constructor
    · -- Prove f (g (x + 2017)) ≥ f x
      rw [h1]
      all_goals
        simp
    · -- Prove f x ≥ f (g x + 2017)
      rw [h2]
      all_goals
        simp
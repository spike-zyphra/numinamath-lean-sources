import Mathlib

theorem algebra_70871 :
    let A := {f : ℝ → ℝ | ∀ x y, f (x * y) = x * f y}
    (∀ f ∈ A, ∀ x y, f (x + y) = f x + f y) ∧
    (∀ g ∈ A, ∀ h ∈ A, (g ∘ h) ∈ A ∧ (g ∘ h) = (h ∘ g)) := by
  intro A
  constructor
  · -- Proof of (a): ∀ f ∈ A, ∀ x y, f (x + y) = f x + f y
    intros f hf x y
    have h1 := hf x 1
    have h2 := hf y 1
    have h3 := hf (x + y) 1
    simp at h1 h2 h3
    linarith
  · -- Proof of (b): ∀ g ∈ A, ∀ h ∈ A, (g ∘ h) ∈ A ∧ (g ∘ h) = (h ∘ g)
    intros g hg h hh
    constructor
    · -- Show that g ∘ h ∈ A.
      intro x y
      simp [Function.comp_apply]
      have h1 : h (x * y) = x * h y := by
        apply hh
      have h2 : g (h (x * y)) = x * g (h y) := by
        rw [show h (x * y) = x * h y by simpa using h1]
        have h3 : g (x * h y) = x * g (h y) := by
          apply hg
        simpa using h3
      linarith [h2]
    · -- Show that g ∘ h = h ∘ g.
      funext z
      simp [Function.comp_apply]
      -- Derive and use linear form of g and h
      have g1 : g z = z * g 1 := by
        specialize hg z 1
        simp at hg
        linarith
      have h1 : h z = z * h 1 := by
        specialize hh z 1
        simp at hh
        linarith
      have g2 : g (h z) = z * g (h 1) := by
        specialize hg z (h 1)
        simp [show h z = z * h 1 by linarith [h1]] at hg ⊢
        linarith
      have h2 : h (g z) = z * h (g 1) := by
        specialize hh z (g 1)
        simp [show g z = z * g 1 by linarith [g1]] at hh ⊢
        linarith
      have eq1 : g (h z) = h (g z) := by
        have hc1 : g (h 1) = h 1 * g 1 := by
          specialize hg (h 1) 1
          simp at hg
          linarith
        have hc2 : h (g 1) = g 1 * h 1 := by
          specialize hh (g 1) 1
          simp at hh
          linarith
        rw [g2, h2, hc1, hc2]
        all_goals ring
      tauto
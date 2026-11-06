import Mathlib

theorem algebra_601870 (f g : ℝ → ℝ) (hf : ∃ x, f x ≠ f 0)
    (hg : ∃ x, g x ≠ g 0) (hfg : ∀ x y, f (x + y) = f x * g y + g x * f y ∧
    g (x + y) = g x * g y - f x * f y) :
    f 0 = 0 ∧ g 0 = 1 := by

  have eq1 := hfg 0 0
  simp at eq1
  have eq2 : f 0 * (1 - 2 * g 0) = 0 := by
    linarith [eq1.1]

  by_cases h : f 0 = 0
  · -- Assume f 0 = 0
    have hf0 : f 0 = 0 := h
    have eq3 : g 0 * (g 0 - 1) = 0 := by
      have eq4 : g 0 = g 0 ^ 2 - f 0 ^ 2 := by
        linarith [eq1.2]
      rw [hf0] at eq4
      nlinarith
    cases (mul_eq_zero.mp eq3) with
    | inl hg0 =>
      have h1 : ∀ x : ℝ, f x = 0 := by
        intro x
        have h1 := hfg x 0
        simp [hf0, hg0, h] at h1
        linarith
      rcases hf with ⟨x, hx⟩
      have h2 := h1 x
      have h3 : f x = f 0 := by
        linarith [h2, hf0]
      contradiction
    | inr hg1 =>
      have h2 : g 0 = 1 := by linarith
      constructor
      · exact hf0
      · exact h2
  · -- Assume f 0 ≠ 0
    have h1 : 1 - 2 * g 0 = 0 := by
      apply (mul_eq_zero.mp eq2).resolve_left
      exact h
    have h2 : g 0 = 1 / 2 := by linarith
    nlinarith [sq_nonneg (f 0), sq_nonneg (g 0 - 1 / 2)]
import Mathlib

theorem algebra_123886 {f g : ℝ → ℝ} (hf : ¬∃ c, ∀ x, f x = c) (hg : ¬∃ c, ∀ x, g x = c)
    (hfg : ∀ x y, f (x + y) = f x * g y + g x * f y ∧ g (x + y) = g x * g y - f x * f y) :
    f 0 = 0 ∧ g 0 = 1 := by
  have h1 := hfg 0 0
  simp at h1
  have h2 : f 0 * (1 - 2 * g 0) = 0 := by 
    linarith
  have h3 : f 0 = 0 ∨ g 0 = 1 / 2 := by 
    cases (mul_eq_zero.mp h2) with
    | inl h4 =>
      left
      linarith
    | inr h5 =>
      right
      linarith
  cases h3 with
  | inl hf00 =>
    have heq2 : g 0 = g 0 ^ 2 := by
      nlinarith [h1.2, hf00]
    have h4 : g 0 * (g 0 - 1) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h4) with
    | inl h4 =>
      have h5 : g 0 = 0 := by linarith
      have h8 : ∃ c, ∀ x, f x = c := by
        use 0
        intro x
        have h6x : f x = 0 := by
          have h7 : f (x + 0) = f x * g 0 + g x * f 0 := by
            specialize hfg x 0
            simpa using hfg.1
          simp [h5, hf00] at h7
          linarith
        assumption
      contradiction
    | inr h4 =>
      have h5 : g 0 = 1 := by linarith
      constructor
      · exact hf00
      · exact h5
  | inr hg0 =>
    -- Case where g(0) = 1/2, so $f(0)^2 = -1/4$ which is a contradiction
    have heq1 : f 0 ^ 2 = -1 / 4 := by
      nlinarith [h1.2, hg0]
    have h0 : f 0 ^ 2 ≥ 0 := by positivity
    nlinarith
import Mathlib

theorem algebra_177140 {f : ℝ → ℝ} (hf1 : f 1 = 0) (hfg : ∀ x y, |f x - f y| = |x - y|) :
    (∀ x, f x = x - 1) ∨ (∀ x, f x = 1 - x) := by
  have h1 : ∀ y, |f y| = |1 - y| := by
    intro y
    have h2 : |f 1 - f y| = |(1 : ℝ) - y| := hfg 1 y
    rw [hf1] at h2
    simpa using h2

  have h2 : f 0 = -1 ∨ f 0 = 1 := by
    have h3 : |f 0| = 1 := by
      specialize h1 0
      norm_num at h1 ⊢
      linarith
    cases' abs_cases (f 0) with h h
    · right
      linarith
    · left
      linarith

  cases h2 with
  | inl h20 =>
    -- Suppose f(0) = -1. Let's show that f(x) = x - 1 for all x.
    have h21 : ∀ x, |f x + 1| = |x| := by
      intro x
      have h40 : |f x - f 0| = |x - (0 : ℝ)| := hfg x 0
      rw [h20] at h40
      have h41 : |f x + 1| = |x| := by
        have h42 : |f x - -1| = |x - (0 : ℝ)| := by simpa using h40
        have h43 : |f x + 1| = |f x - -1| := by
          have : f x + 1 = f x - -1 := by ring
          rw [this]
        rw [h43, h42]
        all_goals
          norm_num
      exact h41

    left
    intro x
    have h30 : |f x| = |1 - x| := h1 x
    have h31 : |f x + 1| = |x| := h21 x
    cases' abs_cases (f x) with h4 h4
    · -- Assume f x ≥ 0
      cases' abs_cases (1 - x) with h5 h5
      · -- Assume 1 - x ≥ 0
        cases' abs_cases (f x + 1) with h6 h6
        · -- Assume f x + 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x + 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
      · -- Assume 1 - x < 0
        cases' abs_cases (f x + 1) with h6 h6
        · -- Assume f x + 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x + 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
    · -- Assume f x < 0
      cases' abs_cases (1 - x) with h5 h5
      · -- Assume 1 - x ≥ 0
        cases' abs_cases (f x + 1) with h6 h6
        · -- Assume f x + 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x + 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
      · -- Assume 1 - x < 0
        cases' abs_cases (f x + 1) with h6 h6
        · -- Assume f x + 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x + 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
  | inr h20 =>
    -- Suppose f(0) = 1. Let's show that f(x) = 1 - x for all x.
    have h21 : ∀ x, |f x - 1| = |x| := by
      intro x
      have h40 : |f x - f 0| = |x - (0 : ℝ)| := hfg x 0
      rw [h20] at h40
      simpa using h40

    right
    intro x
    have h30 : |f x| = |1 - x| := h1 x
    have h31 : |f x - 1| = |x| := h21 x
    cases' abs_cases (f x) with h4 h4
    · -- Assume f x ≥ 0
      cases' abs_cases (1 - x) with h5 h5
      · -- Assume 1 - x ≥ 0
        cases' abs_cases (f x - 1) with h6 h6
        · -- Assume f x - 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x - 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
      · -- Assume 1 - x < 0
        cases' abs_cases (f x - 1) with h6 h6
        · -- Assume f x - 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x - 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
    · -- Assume f x < 0
      cases' abs_cases (1 - x) with h5 h5
      · -- Assume 1 - x ≥ 0
        cases' abs_cases (f x - 1) with h6 h6
        · -- Assume f x - 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x - 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
      · -- Assume 1 - x < 0
        cases' abs_cases (f x - 1) with h6 h6
        · -- Assume f x - 1 ≥ 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
        · -- Assume f x - 1 < 0
          cases' abs_cases (x) with h7 h7
          · -- Assume x ≥ 0
            nlinarith
          · -- Assume x < 0
            nlinarith
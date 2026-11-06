import Mathlib

theorem algebra_199279 {f g : ℝ → ℝ} (hf : ¬∃ c, ∀ x, f x = c)
    (hg : ¬∃ c, ∀ x, g x = c) (hfg : ∀ x y, f (x + y) = f x * g y + g x * f y ∧
    g (x + y) = g x * g y - f x * f y) :
    f 0 = 0 ∧ g 0 = 1 := by
  have h1 := hfg 0 0
  -- For $f$: $f(0 + 0) = f(0) \cdot g(0) + g(0) \cdot f(0)$
  have eq1 : f 0 = f 0 * g 0 + g 0 * f 0 := by
    norm_num at h1
    linarith [h1.1]
  have eq1' : f 0 * (2 * g 0 - 1) = 0 := by
    nlinarith
  -- For $g$: $g(0 + 0) = g(0) \cdot g(0) - f(0) \cdot f(0)$
  have eq2 : g 0 = g 0 * g 0 - f 0 * f 0 := by 
    norm_num at h1
    linarith [h1.2]
  -- Rearranging: $g(0)^2 - g(0) - f(0)^2 = 0$
  have eq2' : g 0 ^ 2 - g 0 - (f 0) ^ 2 = 0 := by 
    nlinarith [eq2]
  by_cases h : f 0 = 0
  · -- Case f 0 = 0
    have h3 : f 0 = 0 := h
    -- From eq2': g 0^2 - g 0 - 0 = 0 => g 0^2 - g 0 = 0
    have h4 : g 0 * (g 0 - 1) = 0 := by
      rw [h] at eq2'
      nlinarith
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case g 0 = 0
      have h5' : g 0 = 0 := h5
      -- If g 0 = 0, then g(x) = 0 for all x
      have h7 : ∀ x, g x = 0 := by
        intro x
        have h2 := hfg x 0
        have eq1 : g (x + 0) = g x * g 0 - f x * f 0 := h2.2
        norm_num [h5', h] at eq1
        linarith
      have h8 : ∃ c, ∀ x, g x = c := by
        use 0
        all_goals
        intro x
        specialize h7 x
        linarith
      contradiction
    · -- Case g 0 - 1 = 0 => g 0 = 1
      have h6' : g 0 = 1 := by linarith 
      constructor
      · exact h3
      · exact h6'
  · -- Case f 0 ≠ 0
    have h6 : 2 * g 0 - 1 = 0 := by
      apply (mul_left_inj' h).mp
      linarith
    -- Thus g 0 = 1/2
    have h7 : g 0 = 1 / 2 := by linarith 
    rw [h7] at eq2'
    nlinarith [sq_nonneg (f 0)]
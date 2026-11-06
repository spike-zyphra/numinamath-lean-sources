import Mathlib

theorem number_theory_215634 (x y : ℤ) :
    y^4 + x^2010 = 2 * y^2 - 1 ↔ (x = 0 ∧ y = -1) ∨ (x = 0 ∧ y = 1) := by
  constructor
  · -- Forward direction: if the equation holds, prove the solutions
    intro h_eq 
    have h1 : (y^2 - 1 : ℤ)^2 + x^2010 = 0 := by
      nlinarith 
    have h2 : (y^2 - 1 : ℤ)^2 ≥ 0 := by
      apply sq_nonneg 
    -- From h1: (y^2 - 1)^2 + x^2010 = 0 
    -- Thus x^2010 ≤ 0 because (y^2 - 1)^2 ≥ 0
    have h3 : x^2010 ≤ 0 := by 
      nlinarith 
    -- Now, show x^2010 ≥ 0.
    have h4 : x^2010 ≥ 0 := by 
      have h5 : x^2010 = (x^1005)^2 := by 
        ring_nf 
      have h6 : (x^1005) ^ 2 ≥ 0 := by 
        apply sq_nonneg 
      linarith [h5, h6] 
    -- Thus, x^2010 = 0 from x^2010 ≤ 0 and x^2010 ≥ 0.
    have h5b : x^2010 = 0 := by 
      linarith 
    -- From h1 and h5b, we can get (y^2 - 1)^2 = 0.
    have h6c : (y^2 - 1 : ℤ) ^ 2 = 0 := by 
      linarith 
    -- From h6c: (y^2 - 1)^2 = 0, we get y^2 - 1 = 0.
    have h7d : (y^2 - 1 : ℤ) = 0 := by 
      nlinarith 
    -- From this, y^2 = 1.
    have h8e : y^2 = 1 := by 
      linarith 
    -- Now we can get x = 0.
    have h11 : x = 0 := by 
      have h12 : x^2010 = 0 := h5b 
      have h13 : x = 0 := by 
        have h14 : x^2010 = 0 := h12
        apply pow_eq_zero 
        exact h14 
      exact h13 
    -- Now we can get y = \pm 1.
    have h10 : y = 1 ∨ y = -1 := by 
      have h18 : y^2 = 1 := h8e 
      have h12 : y = 1 ∨ y = -1 := by 
        have h13 : y^2 - 1 = 0 := by 
          linarith 
        have h14 : (y - 1) * (y + 1) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h14) with h15 h16 
        · -- h15: y - 1 = 0 
          left 
          linarith 
        · -- h16: y + 1 = 0 
          right 
          linarith 
      exact h12 
    cases' h10 with h14 h14 
    · -- When y = 1 
      right 
      exact ⟨h11, h14⟩
    · -- When y = -1 
      left 
      exact ⟨h11, h14⟩ 
  · -- Backward direction: if the solutions hold, prove the equation
    rintro (h | h)
    · -- First solution.
      rcases h with ⟨r1, r2⟩ 
      rw [r1, r2] 
      norm_num 
    · -- Second solution.
      rcases h with ⟨r1, r2⟩ 
      rw [r1, r2] 
      norm_num
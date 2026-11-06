import Mathlib

theorem algebra_19620 : IsLeast {c : ℤ | ∀ x : ℝ, x ^ 2 + 4 * x + c ≠ 0} 5 := by 
  constructor
  · -- Show 5 is in the set
    show ∀ x : ℝ, x ^ 2 + 4 * x + (5 : ℤ) ≠ 0
    intro x
    have h1 : (x + 2) ^ 2 ≥ 0 := by
      apply sq_nonneg
    have h2 : x ^ 2 + 4 * x + (5 : ℤ) ≥ 1 := by
      have h3 : x ^ 2 + 4 * x + (5 : ℤ) = (x + 2) ^ 2 + 1 := by
        ring_nf
      rw [h3]
      linarith [h1]
    have h3 : x ^ 2 + 4 * x + (5 : ℤ) ≠ 0 := by
      linarith [h2]
    exact h3
  · -- Show no integer less than 5 is in the set
    intro c hc
    have h : ∀ x : ℝ, x ^ 2 + 4 * x + (c : ℤ) ≠ 0 := by
      simpa using hc
    by_contra h'
    push_neg at h'
    have h3 : c ≤ 4 := by
      omega
    have h4 : (c : ℝ) ≤ (4 : ℝ) := by
      exact_mod_cast (show (c : ℤ) ≤ 4 by omega)
    have h5 : ∃ x : ℝ, x ^ 2 + 4 * x + (c : ℤ) = 0 := by
      have h7 : (16 : ℝ) - 4 * (c : ℝ) ≥ 0 := by
        have h8 : (c : ℝ) ≤ (4 : ℝ) := by
          exact_mod_cast (show (c : ℤ) ≤ 4 by omega)
        nlinarith
      use (-2 + Real.sqrt ((4 - (c : ℝ)) : ℝ) )
      nlinarith [ Real.sqrt_nonneg ((4 - (c : ℝ)) : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (4 - (c : ℝ)) by nlinarith) ]
    rcases h5 with ⟨x, hx⟩
    have h8 : x ^ 2 + 4 * x + (c : ℤ) = 0 := by
      simpa using hx
    have h9 : x ^ 2 + 4 * x + (c : ℤ) ≠ 0 := h x
    contradiction
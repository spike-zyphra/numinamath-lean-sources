import Mathlib

theorem algebra_302533 (a : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 - 2 * x + a)
    (h : {x | f x = x} = {x | f (f x) = x}) :
    a ≥ 5 / 4 := by

  have h1 : {x | f x = x} = {x | f (f x) = x} := h 
  have h2 : ∀ x : ℝ, f x = x ↔ f (f x) = x := by 
    intro x 
    have h3 : x ∈ {x | f x = x} ↔ x ∈ {x | f (f x) = x} := by 
      rw [h1]
    simpa using h3 

  by_contra h'
  push_neg at h'
  -- Now h' : a < 5 / 4 := h'
  have h3 : a < 5 / 4 := h'

  -- Now, we need to construct an x such that f(f(x)) = x and f(x) ≠ x, a contradiction

  have h4 : ∃ x, f (f x) = x ∧ f x ≠ x := by 
    have h5 : 5 - 4 * a > 0 := by 
      linarith 
    use (1 - Real.sqrt (5 - 4 * a)) / 2 
    constructor 
    · -- Show f (f x) = x
      have h6 : f ((1 - Real.sqrt (5 - 4 * a)) / 2) = 1 - ((1 - Real.sqrt (5 - 4 * a)) / 2) := by 
        rw [hf]
        simp 
        nlinarith [ Real.sqrt_nonneg (5 - 4 * a), Real.sq_sqrt (show 0 ≤ (5 - 4 * a) by linarith) ]
      have h7 : f (f ((1 - Real.sqrt (5 - 4 * a)) / 2)) = ( (1 - Real.sqrt (5 - 4 * a)) / 2 ) := by 
        rw [h6]
        rw [hf]
        simp 
        nlinarith [ Real.sqrt_nonneg (5 - 4 * a), Real.sq_sqrt (show 0 ≤ (5 - 4 * a) by linarith) ]
      linarith 
    · -- Show f x ≠ x 
      intro h_eq 
      have h6 : f ((1 - Real.sqrt (5 - 4 * a)) / 2) = 1 - ((1 - Real.sqrt (5 - 4 * a)) / 2) := by 
        rw [hf]
        simp 
        nlinarith [ Real.sqrt_nonneg (5 - 4 * a), Real.sq_sqrt (show 0 ≤ (5 - 4 * a) by linarith) ]
      rw [h_eq] at h6 
      -- Now h6 is 1 - ((1 - Real.sqrt (5 - 4 * a)) / 2) = (1 - Real.sqrt (5 - 4 * a)) / 2
      nlinarith [ Real.sqrt_nonneg (5 - 4 * a), Real.sq_sqrt (show 0 ≤ (5 - 4 * a) by linarith), Real.sqrt_pos.mpr (show 0 < (5 - 4 * a) by linarith) ]

  rcases h4 with ⟨x, hfx1, hfx2⟩

  have h5 : f x = x := by 
    have eq1 := h2 x 
    tauto

  contradiction
import Mathlib

theorem algebra_246907 (a : ℕ → ℝ) (ha : ∀ n, a (n + 1) = 2005 * a n / (2003 * a n + 2005)) (ha1 : a 1 = 1) :
    a 2006 = 1 / 2004 := by
  have h1 : ∀ (n : ℕ), a n = 2005 / (2 + (n : ℝ) * 2003) := by 
    intro n 
    induction n with 
    | zero => 
      have h2 : a 0 = 2005 / 2 := by 
        have h3 : a 1 = 1 := ha1 
        have h4 : a 1 = 2005 * a 0 / (2003 * a 0 + 2005) := by
          specialize ha 0 
          simpa using ha 
        rw [h3] at h4 
        have h5 : (2003 * a 0 + 2005 : ℝ) ≠ 0 := by 
          by_contra h 
          have : a 0 = -2005 / 2003 := by
            nlinarith 
          rw [this] at h4 
          norm_num at h4 
        field_simp [h5] at h4 
        linarith 
      rw [h2] 
      all_goals norm_num 
    | succ k ih => 
      have h7 : a (k + 1) = 2005 * a k / (2003 * a k + 2005) := by
        specialize ha k 
        simpa using ha 
      rw [h7] 
      rw [ih] 
      field_simp 
      ring 
  have h2006 : a 2006 = 2005 / (2 + (2006 : ℝ) * 2003) := h1 2006 
  rw [h2006] 
  field_simp 
  <;> norm_num
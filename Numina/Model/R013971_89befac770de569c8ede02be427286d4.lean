import Mathlib

theorem number_theory_80848 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime)
    (h1 : p * q + q * r + r * p = 191) (h2 : p + q = r - 1) : p + q + r = 25 := by
  rcases hpqr with ⟨hp, hq, hr⟩
  by_cases h3 : r > 1 
  · -- Case r > 1, r-1 is well-defined
    have h4 : r = p + q + 1 := by
      omega 
    rw [h4] at h1 
    have h5 : p ≥ 2 := by 
      by_contra h 
      push_neg at h 
      have : p < 2 := by linarith 
      interval_cases p <;> norm_num at hp 
    have h6 : q ≥ 2 := by 
      by_contra h 
      push_neg at h 
      have : q < 2 := by linarith 
      interval_cases q <;> norm_num at hq 
    have h7 : p ≤ 13 := by 
      nlinarith [show q ≥ 2 by linarith [h6]]
    have h8 : q ≤ 13 := by 
      nlinarith [show p ≥ 2 by linarith [h5]]
    interval_cases p <;> interval_cases q 
    <;> norm_num at h1 hp hq h4
    <;> try { 
      have h5r : r = 13 := by 
        omega 
      rw [h5r]
      all_goals norm_num 
    }
  · -- Case r ≤ 1, r= 0 or 1.
    have h4 : r ≤ 1 := by omega 
    have h5 : r ≤ 1 := by omega 
    have h6 : r < 2 := by 
      omega 
    interval_cases r <;> norm_num at hr 
    all_goals linarith
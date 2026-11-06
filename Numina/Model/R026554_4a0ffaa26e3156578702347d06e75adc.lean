import Mathlib

theorem algebra_240064 (x y : ℤ) :
    6 * x ^ 2 * y ^ 2 - 4 * y ^ 2 = 2012 - 3 * x ^ 2 ↔
    (x, y) = (2, 10) ∨ (x, y) = (-2, 10) ∨ (x, y) = (2, -10) ∨ (x, y) = (-2, -10) := by
  constructor
  · -- Assume the equation holds, prove the four solutions
    intro h
    have h1 : (3 * x ^ 2 - 2) * (2 * y ^ 2 + 1) = 2010 := by
      nlinarith
    have h2 : (3 * x ^ 2 - 2) ∣ 2010 := by 
      use 2 * y ^ 2 + 1
      all_goals linarith
    have h3 : (3 * x ^ 2 - 2) ≥ 1 := by
      have h4 : (3 * x ^ 2 - 2) > 0 := by
        by_contra h5
        push_neg at h5
        have h6 : (3 * x ^ 2 - 2) ≤ 0 := by linarith
        have h7 : (2 * y ^ 2 + 1) > 0 := by 
          nlinarith [sq_nonneg y]
        nlinarith [show (3 * x ^ 2 - 2) * (2 * y ^ 2 + 1) = 2010 from h1]
      linarith
    have h4 : (3 * x ^ 2 - 2) ≤ 2010 := by 
      apply Int.le_of_dvd (by norm_num) h2
    have h5 : x ≤ 26 := by
      nlinarith [sq_nonneg x, h1]
    have h6 : x ≥ -26 := by 
      nlinarith [sq_nonneg x, h1]
    interval_cases x <;> try { 
      norm_num [Prod.ext_iff] at *
      <;> try { 
        have : y ≤ 32 := by 
          nlinarith 
        have : y ≥ -32 := by 
          nlinarith
        interval_cases y <;> norm_num [Prod.ext_iff] at *
      }
    }
  · -- Assume the four solutions, prove the equation
    rintro (h | h | h | h)
    · -- (2, 10)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- (-2, 10)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- (2, -10)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
    · -- (-2, -10)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
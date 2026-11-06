import Mathlib

theorem algebra_136846 (x y : ℤ) :
    3 * x * y + 2 * x + y = 12 ↔
    (x, y) = (-1, -7) ∨ (x, y) = (-13, -1) ∨ (x, y) = (6, 0) ∨ (x, y) = (0, 12) := by 
  constructor
  · -- Assume 3 * x * y + 2 * x + y = 12 prove the disjunction
    rintro h
    have h1 : (3 * x + 1) * y = -2 * x + 12 := by 
      nlinarith
    have h2 : (3 * x + 1) ∣ 38 := by
      use (y * 3 + 2)
      nlinarith
    have h3 : (3 * x + 1) ≤ 38 := by 
      apply Int.le_of_dvd (by norm_num) h2
    have h4 : (3 * x + 1) ≥ -38 := by 
      have h5 : (- (3 * x + 1)) ∣ 38 := by 
        exact Int.neg_dvd.2 h2
      have h6 : - (3 * x + 1) ≤ 38 := by 
        apply Int.le_of_dvd (by norm_num) h5
      linarith
    have h5 : x ≥ -13 := by 
      omega
    have h6 : x ≤ 12 := by
      omega
    interval_cases x <;> norm_num [Prod.ext_iff] at h1 ⊢ 
    <;> omega 
  · -- The converse: each of the solutions satisfies the equation
    rintro (h | h | h | h)
    · -- (-1, -7)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (-13, -1)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (6, 0)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
    · -- (0, 12)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals norm_num
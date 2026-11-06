import Mathlib

theorem algebra_299800 (x y : ℤ) : x^2 = y^2 + 2 * y + 13 ↔
    (x, y) = (4, -3) ∨ (x, y) = (4, 1) ∨ (x, y) = (-4, 1) ∨ (x, y) = (-4, -3) := by
  constructor
  · -- Assume the equation holds, prove the four cases
    intro h
    have h1 : x^2 - (y + 1)^2 = 12 := by
      nlinarith
    have h2 : (x - (y + 1)) * (x + (y + 1)) = 12 := by
      ring_nf at h1 ⊢
      linarith
    have h3 : x - (y + 1) ∣ 12 := by
      use x + (y + 1)
      all_goals linarith
    have h4 : x - (y + 1) ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : x - (y + 1) ≥ -12 := by 
      have h6 : - (x - (y + 1)) ∣ 12 := by 
        exact Int.neg_dvd.2 h3
      have h7 : - (x - (y + 1)) ≤ 12 := by 
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases h6 : x - (y + 1) <;> norm_num [Prod.ext_iff] at *
    <;> try { omega }
  · -- Assume the four cases, prove the equation
    rintro (h | h | h | h)
    · -- Case (4, -3)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (4, 1)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (-4, 1)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
    · -- Case (-4, -3)
      simp [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      all_goals norm_num
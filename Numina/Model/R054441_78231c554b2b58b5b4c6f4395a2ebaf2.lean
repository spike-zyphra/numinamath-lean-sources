import Mathlib

theorem algebra_188722 (x y : ℤ) :
    2 * x ^ 3 + x * y - 7 = 0 ↔
    (x, y) = (1, 5) ∨ (x, y) = (7, -97) ∨ (x, y) = (-1, -9) ∨ (x, y) = (-7, -99) := by
  constructor
  · -- Forward direction: If 2x^3 + x*y - 7 = 0 then (x,y) is one of the four given solutions
    rintro h
    have h1 : x * (2 * x ^ 2 + y) = 7 := by 
      linarith 
    have h2 : x ∣ 7 := by 
      use (2 * x ^ 2 + y)
      linarith 
    have h3 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by 
      have h4 : x ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h2 
      have h5 : x ≥ -7 := by 
        have h5 : (-x) ∣ 7 := by 
          exact Int.neg_dvd.2 h2 
        have h6 : -x ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h5 
        linarith 
      interval_cases x <;> tauto 
    rcases h3 with (rfl | rfl | rfl | rfl)
    · -- Case x = 1
      have hy : y = 5 := by 
        nlinarith 
      simp [hy] 
    · -- Case x = -1
      have hy : y = -9 := by 
        nlinarith 
      simp [hy] 
    · -- Case x = 7
      have hy : y = -97 := by 
        nlinarith 
      simp [hy] 
    · -- Case x = -7
      have hy : y = -99 := by 
        nlinarith 
      simp [hy] 
  · -- Backward direction: If (x,y) is one of the four given solutions then 2x^3 + x*y - 7 = 0
    rintro (h | h | h | h)
    · -- (1, 5)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (7, -97)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-1, -9)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (-7, -99)
      simp [Prod.mk.injEq] at h 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num
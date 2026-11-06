import Mathlib

theorem algebra_2324 :
  {n : ℤ | IsSquare (n^2 - 13 * n + 50)} = {-1, 14} := by 
  ext n 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor 
  · -- Assume n^2 -13n + 50 is a perfect square, prove n = -1 or 14
    intro h 
    rcases h with ⟨k, hk⟩
    have h1 : k^2 = n^2 - 13 * n + 50 := by 
      nlinarith
    -- Equation becomes (2n-13-2k)(2n-13+2k) = -31
    have h2 : (2 * n - 13 - 2 * k) * (2 * n - 13 + 2 * k) = -31 := by
      nlinarith 
    -- so $(2n-13-2k)$ divides $31$
    have h4 : (2 * n - 13 - 2 * k) ∣ 31 := by 
      use -(2 * n - 13 + 2 * k)
      all_goals 
        nlinarith 
    -- so $(2n-13-2k)$ is in [-31, -23], bUt since k is integer we need consider these
    have h9 : (2 * n - 13 - 2 * k) ≤ 31 := by
      apply Int.le_of_dvd (by norm_num) h4
    have h10 : (2 * n - 13 - 2 * k) ≥ -31 := by
      have h22 : -(2 * n - 13 - 2 * k) ∣ 31 := by 
        exact Int.neg_dvd.2 h4 
      have h23 : -(2 * n - 13 - 2 * k) ≤ 31 := by 
        apply Int.le_of_dvd (by norm_num) h22 
      omega
    interval_cases h15 : (2 * n - 13 - 2 * k) <;> try { 
      omega 
    } <;> try { 
      -- so if d divides 31. So all k is bounded. So $k ≤ 8$
      have hk2 : k ≤ 16 := by nlinarith 
      have hk3 : k ≥ -16 := by nlinarith 
      interval_cases k <;> omega 
    }
  · -- Assume n = -1 or 14, prove n^2 -13n + 50 is a perfect square
    rintro (rfl | rfl)
    · -- Check n = -1 
      native_decide 
    · -- Check n = 14 
      native_decide
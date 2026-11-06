import Mathlib

theorem algebra_18871 :
    IsLeast {x : ℕ | x > 9 ∧ ⌊(x : ℝ)⌋ - 19 * ⌊(x : ℝ) / 19⌋ = 9 ∧ ⌊(x : ℝ)⌋ - 89 * ⌊(x : ℝ) / 89⌋ = 9} 1700 := by 
  constructor 
  · -- Show 1700 is in the set
    constructor 
    · norm_num -- 1700 > 9
    constructor
    · norm_num -- Check the first equation
    · norm_num -- Check the second equation
  · -- Show it's the smallest
    intro y hy
    rcases hy with ⟨hy1, hy2, hy3⟩
    by_contra h
    push_neg at h
    -- y < 1700
    have h11 : (y : ℝ) < (1700 : ℝ) := by
      exact_mod_cast h
    have eq1 : (y : ℤ) - 19 * (y / 19 : ℤ) = 9 := by 
      have h2 : ⌊(y : ℝ)⌋ - 19 * ⌊(y : ℝ) / 19⌋ = 9 := hy2
      have eq3 : ⌊(y : ℝ)⌋ = (y : ℤ) := by 
        simp
      have eq4 : ⌊(y : ℝ) / (19 : ℝ)⌋ = (y / 19 : ℤ) := by 
        have h_eq : ⌊(y : ℝ) / (19 : ℝ)⌋ = (y / 19 : ℤ) := by 
          have h1 : ⌊(y : ℝ) / (19 : ℝ)⌋ = (y / 19 : ℤ) := by 
            have h2 : ∀ (y : ℕ), ⌊(y : ℝ) / (19 : ℝ)⌋ = (y / 19 : ℤ) := by 
              intro y
              have h3 : ⌊(y : ℝ) / (19 : ℝ)⌋ = (y / 19 : ℤ) := by 
                norm_num [Int.floor_eq_iff]
                <;> ring_nf <;> norm_num
                <;> try { omega }
              simpa using h3
            specialize h2 y
            simpa using h2
          exact h1
        exact h_eq
      rw [eq3, eq4] at h2
      exact_mod_cast h2
    -- Second equation
    have eq2 : (y : ℤ) - 89 * (y / 89 : ℤ) = 9 := by 
      have h4 : ⌊(y : ℝ)⌋ - 89 * ⌊(y : ℝ) / 89⌋ = 9 := hy3
      have eq3 : ⌊(y : ℝ)⌋ = (y : ℤ) := by 
        simp
      have eq5 : ⌊(y : ℝ) / (89 : ℝ)⌋ = (y / 89 : ℤ) := by 
        have h_eq : ⌊(y : ℝ) / (89 : ℝ)⌋ = (y / 89 : ℤ) := by 
          have h1 : ⌊(y : ℝ) / (89 : ℝ)⌋ = (y / 89 : ℤ) := by 
            have h2 : ∀ (y : ℕ), ⌊(y : ℝ) / (89 : ℝ)⌋ = (y / 89 : ℤ) := by 
              intro y
              have h3 : ⌊(y : ℝ) / (89 : ℝ)⌋ = (y / 89 : ℤ) := by 
                norm_num [Int.floor_eq_iff]
                <;> ring_nf <;> norm_num
                <;> try { omega }
              simpa using h3
            specialize h2 y
            simpa using h2
          exact h1
        exact h_eq
      rw [eq3, eq5] at h4
      exact_mod_cast h4
    have h12 : y ≤ 1699 := by 
      omega 
    interval_cases y <;> norm_num at eq1 eq2 hy1 <;> omega
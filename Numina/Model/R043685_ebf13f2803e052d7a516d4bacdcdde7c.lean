import Mathlib

theorem algebra_20965 :
    IsGreatest {x | ∃ a b c : ℤ, 100 * a + 10 * b + c = x ∧ 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧ ∃ r : ℚ, a = 4 * r ∧ b = a * r ∧ ∃ d, c = b + d ∧ 5 = c + d} 697 := by
  constructor
  · -- Show that 697 is in the set
    use 6, 9, 7 
    constructor
    · -- 100 * a + 10 * b + c = 697
      norm_num 
    constructor
    · -- 1 ≤ a 
      norm_num 
    constructor
    · -- a ≤ 9 
      norm_num 
    constructor
    · -- 0 ≤ b 
      norm_num 
    constructor
    · -- b ≤ 9 
      norm_num 
    constructor
    · -- 0 ≤ c 
      norm_num 
    constructor
    · -- c ≤ 9 
      norm_num 
    use (3 / 2 : ℚ)
    constructor
    · -- a = 4 * r 
      norm_num 
    constructor
    · -- b = a * r 
      norm_num 
    use -2 
    all_goals norm_num 
  · -- Show that 697 is greatest in the set 
    intro x h 
    rcases h with ⟨a, b, c, hx_eq, h1, h2, h3, h4, h5, h6, r, ha, hb, d, hc, hd⟩
    have eq1 : (4 * (b : ℚ) ) = (a : ℚ) ^ 2 := by 
      have r_eq : r = (a : ℚ) / 4 := by 
        have hr : (a : ℚ) = 4 * r := by 
          simpa using ha 
        linarith 
      rw [r_eq] at hb 
      have eq2 : (b : ℚ) = (a : ℚ) * ((a : ℚ) / 4) := by 
        simpa using hb 
      have eq3 : (4 * (b : ℚ) ) = 4 * ((a : ℚ) * ((a : ℚ) / 4)) := by 
        rw [eq2] 
      have eq4 : 4 * ((a : ℚ) * ((a : ℚ) / 4)) = (a : ℚ) ^ 2 := by 
        ring_nf 
      linarith [eq3, eq4] 
    have eq3 : 4 * (b : ℤ) = (a : ℤ) ^ 2 := by 
      exact_mod_cast eq1 
    have h7 : a ≤ 6 := by 
      nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), h4, eq3] 
    have h8 : a ≥ 1 := h1 
    interval_cases a <;> try { 
      omega 
    } 
    <;> try { 
      norm_num at eq3 
      have h11 : b ≤ 9 := h4 
      have h12 : b ≥ 0 := h3 
      interval_cases b <;> try { 
        omega 
      } 
    }
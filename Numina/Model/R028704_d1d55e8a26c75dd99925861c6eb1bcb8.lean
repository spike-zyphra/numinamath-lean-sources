import Mathlib

theorem number_theory_4813 {a b : ℤ} (_ : 0 < a) (hb : 0 < b) :
    ∃ q r e, a = b*q+e*r ∧ (e = 1 ∨ e = -1) ∧ -b/2 < e*r ∧ e*r ≤ b/2 := by
  have h1 : b > 0 := by linarith
  have h2 : ∃ q r, a = b * q + r ∧ 0 ≤ r ∧ r < b := by
    use a / b, a % b
    constructor
    · -- a = b * (a / b) + (a % b)
      rw [Int.ediv_add_emod a b]
    constructor
    · -- Show 0 ≤ a % b
      have h3 : a % b ≥ 0 := by 
        apply Int.emod_nonneg 
        all_goals omega
      omega
    · -- Show a % b < b
      have h4 : a % b < b := by 
        apply Int.emod_lt_of_pos 
        all_goals omega 
      omega
  rcases h2 with ⟨q, r, ha_eq, hr1, hr2⟩
  by_cases h4 : r ≤ b / 2
  · -- Case 1: r ≤ b / 2
    use q
    use r
    use 1 
    constructor 
    · -- a = b*q + 1*r 
      linarith 
    constructor 
    · -- 1 = 1 ∨ 1 = -1 
      left 
      norm_num 
    constructor 
    · -- -b/2 < 1*r 
      omega 
    · -- 1*r ≤ b/2 
      omega 
  · -- Case 2: r > b / 2 
    push_neg at h4 
    use q + 1 
    use (b - r) 
    use -1 
    constructor 
    · -- a = b*(q+1) + (-1)*(b-r) 
      linarith 
    constructor 
    · -- -1 = 1 ∨ -1 = -1 
      right 
      norm_num 
    constructor 
    · -- -b/2 < (-1)*(b-r) 
      omega 
    · -- (-1)*(b-r) ≤ b/2 
      omega
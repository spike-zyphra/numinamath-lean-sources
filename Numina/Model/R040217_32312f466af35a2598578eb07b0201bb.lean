import Mathlib

theorem algebra_62717 {x : ℝ} : ⌊x⌋ * (x - ⌊x⌋) = 1991 * x ↔ x = 0 ∨ x = -1 / 1992 := by 
  constructor
  · -- Assume ⌊x⌋ * (x - ⌊x⌋) = 1991 * x, prove x = 0 or x = -1/1992
    intro h
    have h1 : ⌊x⌋ ≤ (x : ℝ) := by exact_mod_cast Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast Int.lt_floor_add_one x
    have h3 : (⌊x⌋ : ℝ) * (x - ⌊x⌋ : ℝ) = 1991 * x := by 
      simpa using h
    by_cases h4 : x = 0
    · -- Case where x = 0, trivial solution
      left
      exact h4
    · -- Assume x ≠ 0, need to derive x = -1/1992
      have h4 : x ≠ 0 := by
        intro hx
        contradiction
      have h6 : ⌊x⌋ ≤ 0 := by
        by_contra h7
        push_neg at h7
        have h7' : ⌊x⌋ ≥ 1 := by omega
        have h7'' : (⌊x⌋ : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h7'
        nlinarith [h3, h1, h2, sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ)), h4]
      have h7 : ⌊x⌋ ≥ -1 := by
        by_contra h8
        push_neg at h8
        have h8' : ⌊x⌋ ≤ -2 := by omega
        have h8'' : (⌊x⌋ : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast h8'
        nlinarith [h3, h1, h2, sq_nonneg (x - (⌊x⌋ : ℝ)), sq_nonneg ((⌊x⌋ : ℝ)), h4]
      have h8 : ⌊x⌋ = 0 ∨ ⌊x⌋ = -1 := by 
        omega
      rcases h8 with h8 | h8
      · -- ⌊x⌋ = 0
        have h8' : (⌊x⌋ : ℝ) = (0 : ℝ) := by exact_mod_cast h8
        have h9 : x = 0 := by 
          nlinarith [h3, h8', h1, h2]
        contradiction
      · -- ⌊x⌋ = -1
        have h8' : (⌊x⌋ : ℝ) = (-1 : ℝ) := by exact_mod_cast h8
        have h9 : x = -1 / 1992 := by 
          nlinarith [h3, h8', h1, h2]
        right
        linarith
  · -- Assume x = 0 ∨ x = -1/1992, prove ⌊x⌋ * (x - ⌊x⌋) = 1991 * x
    rintro (h | h)
    · -- x = 0
      rw [h]
      norm_num
      <;> try { tauto }
    · -- x = -1/1992
      rw [h]
      norm_num
      <;> try { tauto }
      all_goals norm_num
      all_goals try { nlinarith }
      all_goals try { norm_num }
      all_goals try { tauto }
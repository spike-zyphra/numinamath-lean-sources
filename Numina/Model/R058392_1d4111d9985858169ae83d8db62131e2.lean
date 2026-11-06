import Mathlib

theorem number_theory_217506 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : 24 * m = n ^ 4) :
    IsLeast {m' | 0 < m' ∧ ∃ n : ℕ, 24 * m' = n ^ 4} 54 := by
  constructor
  · -- Let's show that 54 is in the set.
    constructor
    · norm_num
    · use 6
      all_goals norm_num
  · -- Let's show that 54 is the minimum in the set.
    intro m' h1 
    rcases h1 with ⟨hm', n', h2⟩ 
    by_contra h'
    push_neg at h'
    -- So we have m' < 54, 0 < m', and 24 * m' = n' ^ 4
    -- Let's show that this leads to a contradiction
    have h2' : m' < 54 := by 
      nlinarith 
    -- Then n' < 6
    have h3 : n' < 6 := by 
      by_contra h4 
      push_neg at h4 
      have h4' : n' >= 6 := by linarith 
      have h4'' : n' ^ 4 >= 6 ^ 4 := by 
        have h5 : n' >= 6 := h4' 
        have : n' ^ 4 >= 6 ^ 4 := by 
          apply Nat.pow_le_pow_of_le_left 
          linarith 
        linarith 
      have h6 : 24 * m' >= 1296 := by 
        linarith [h2, h4''] 
      have h7 : 24 * m' < 1296 := by 
        have h7' : m' < 54 := h2' 
        omega 
      linarith 
    interval_cases n' <;> omega 
    all_goals linarith
    all_goals nlinarith
    <;> linarith
    all_goals try { contradiction }
    all_goals try { linarith }
    all_goals nlinarith
    <;> try { omega }
    all_goals try { nlinarith }
    <;> try { ring_nf <;> nlinarith }
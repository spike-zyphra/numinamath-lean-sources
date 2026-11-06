import Mathlib

theorem number_theory_289805 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a < b ∧ b < c ∧ a + b + c = 100 ∧ a * b * c = 18018}.ncard = 2 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a < b ∧ b < c ∧ a + b + c = 100 ∧ a * b * c = 18018} = {(11, 26, 63), (13, 21, 66)} := by
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Assume h: ⟨a, b, c⟩ is a solution
      rintro ⟨ha, hb, hc, h1, h2, h3, h4⟩
      have h5 : a < 34 := by
        nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      have h6 : b < 50 := by
        nlinarith [show a < 34 from by nlinarith, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
      interval_cases a <;> try { 
        omega 
      }
      <;> try { 
        interval_cases b <;> omega 
      }
      <;> try { 
        all_goals 
          norm_num at h4 
          <;> try { 
            omega 
          } <;> try { 
            have hx : c = 100 - a - b := by linarith 
            rw [hx] at h4 
            all_goals 
              nlinarith 
          }
      }
      <;> omega
      <;> norm_num
      <;> omega 
      <;> norm_num 
      <;> omega 
      <;> norm_num 
      <;> omega 
      <;> norm_num 
      <;> omega
    · -- Assume ⟨a, b, c⟩ is either (11, 26, 63) or (13, 21, 66)
      rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
      · -- Show (11, 26, 63) in the set
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Show (13, 21, 66) in the set
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_pair]
  all_goals
    norm_num
  all_goals
    tauto
  all_goals
    norm_num
  all_goals
    tauto
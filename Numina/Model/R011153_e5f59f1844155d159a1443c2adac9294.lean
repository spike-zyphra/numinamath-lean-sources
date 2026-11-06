import Mathlib

-- we show a simple lemma for the condition of being a perfect square
lemma is_sq_eq_sq_of_pos (x: ℤ) (h: IsSquare x): ∃ r, 0 ≤ r ∧ x = r ^ 2 := by
  apply IsSquare.exists_sq at h
  obtain ⟨r, hr⟩ := h
  by_cases l: 0 ≤ r
  .
    use r
  .
    set t:= -r
    use t
    constructor
    .
      simp at l
      simp [t]
      linarith
    .
      simp [t]
      nlinarith

theorem number_theory_623651: IsLeast {k: ℤ | ∃ a b c, k = a + b + c ∧ 0 < a ∧ a < b ∧ b < c ∧
  IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (b + c)} 55 := by

  constructor
  · -- Show 55 is in the set
    use 6, 19, 30
    all_goals
      native_decide
  · -- Show no value less than 55 is in the set
    intro k hk
    rcases hk with ⟨a, b, c, h_eq, ha1, hab, hbc, h1, h2, h3⟩
    by_contra h4
    push_neg at h4
    have h5 : k < 55 := by linarith 
    rw [h_eq] at h5
    have h7 : a + b < 55 := by
      nlinarith 
    have h8 : a + c < 55 := by
      nlinarith 
    have h9 : b + c < 55 := by
      nlinarith 
    rcases (is_sq_eq_sq_of_pos (a + b) h1) with ⟨s1, hs1, he1⟩
    rcases (is_sq_eq_sq_of_pos (a + c) h2) with ⟨s2, hs2, he2⟩
    rcases (is_sq_eq_sq_of_pos (b + c) h3) with ⟨s3, hs3, he3⟩
    have h11 : s1 < 8 := by 
      nlinarith 
    have h12 : s2 < 8 := by 
      nlinarith 
    have h13 : s3 < 8 := by
      nlinarith 
    have h8 : a < b := hab 
    have h9 : b < c := hbc 
    -- Show s1 < s2 < s3
    have h20 : a + b < a + c := by linarith 
    have h21 : a + c < b + c := by linarith
    have h22 : s1 < s2 := by
      nlinarith [he1, he2]
    have h23 : s2 < s3 := by 
      nlinarith [he2, he3]
    interval_cases s1 <;> try { 
      omega 
    } 
    <;> try { 
        interval_cases s2 <;> try { 
          omega 
        } 
        <;> try { 
            interval_cases s3 <;> omega 
        }
    }
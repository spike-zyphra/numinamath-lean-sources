import Mathlib

theorem number_theory_62907 :
    IsLeast {n : ℕ | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ n = a + b + c ∧  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (b + c)} 55 := by
  constructor
  · -- Show that 55 is a valid integer
    use 6, 19, 30
    all_goals
      native_decide
  · -- Show that 55 is the smallest such integer
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, hn, hne1, hne2, hne3, hsq1, hsq2, hsq3⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 55 := by
      omega
    rcases hsq1 with ⟨s1, hs1⟩
    rcases hsq2 with ⟨s2, hs2⟩
    rcases hsq3 with ⟨s3, hs3⟩
    have h2 : a + b ≤ 53 := by
      omega
    have h3 : a + c ≤ 53 := by
      omega
    have h4 : b + c ≤ 53 := by
      omega
    have h5 : 1 ≤ a + b := by
      omega
    have h6 : 1 ≤ a + c := by
      omega
    have h7 : 1 ≤ b + c := by
      omega
    have h8 : s1 ≤ 7 := by
      nlinarith
    have h9 : s2 ≤ 7 := by
      nlinarith
    have h10 : s3 ≤ 7 := by
      nlinarith
    interval_cases s1 <;> try { 
      omega 
    } 
    <;> try { 
      interval_cases s2 <;> try { 
        omega 
      } 
      <;> try { 
        interval_cases s3 <;> try { 
          omega 
        } 
      }
    }
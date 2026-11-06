import Mathlib

theorem number_theory_57309 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      IsSquare (a + b) ∧ IsSquare (a + c) ∧ IsSquare (b + c) ∧ x = a + b + c} 55 := by
  constructor
  · -- Show that 55 is in the set
    use 6, 19, 30
    all_goals native_decide
    all_goals norm_num [IsSquare]
    all_goals try native_decide
    all_goals norm_num [IsSquare]
    all_goals norm_num
  · -- Show that any number in the set is >= 55
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hne1, hne2, hne3, hsq1, hsq2, hsq3, hx⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 55 := by 
      omega
    have h2 : a ≤ 53 := by
      omega
    have h3 : b ≤ 53 := by
      omega
    have h4 : c ≤ 53 := by
      omega
    obtain ⟨r1, hr1⟩ := hsq1
    obtain ⟨r2, hr2⟩ := hsq2
    obtain ⟨r3, hr3⟩ := hsq3
    have hr1' : r1 ≤ 7 := by
      nlinarith
    have hr2' : r2 ≤ 7 := by
      nlinarith
    have hr3' : r3 ≤ 7 := by
      nlinarith
    interval_cases r1 <;> interval_cases r2 <;> interval_cases r3 <;> try { 
      omega
    } <;> norm_num at hr1 hr2 hr3 <;> try { contradiction }
    <;> try { contradiction }
    <;> try { 
      exfalso 
      <;> try { 
        all_goals 
        try { 
          omega 
        } 
        <;> try { 
          contradiction 
        } 
      } 
    } 
    <;> try { 
      exfalso 
      <;> try { 
        exfalso 
        <;> try { 
          tauto 
        } 
      } 
    } 
    <;> try { 
      exfalso 
      <;> try { 
        exfalso 
        <;> try { 
          tauto 
        } 
        <;> try { 
          nlinarith 
        } 
      } 
    } 
    <;> try { 
      exfalso 
      <;> try { 
        exfalso 
        <;> try { 
          tauto 
        } 
        <;> try { 
          nlinarith 
        } 
      } 
    }
    all_goals try { 
      exfalso 
      <;> try { 
        tauto 
      } 
      <;> try { 
        exfalso 
      } 
      <;> try { 
        exfalso 
        <;> tauto 
        <;> nlinarith 
      } 
    }
  all_goals try { contradiction }
  all_goals try { norm_num }
  all_goals try { norm_num }
  all_goals try { nlinarith }
  all_goals try { norm_num }
  all_goals try { nlinarith }
  all_goals try { 
    exfalso 
    <;> try { 
      exfalso 
      <;> try { 
        exfalso 
        <;> tauto 
      } 
    } 
    <;> try { 
      exfalso 
      <;> try { 
        tauto 
      } 
    } 
  }
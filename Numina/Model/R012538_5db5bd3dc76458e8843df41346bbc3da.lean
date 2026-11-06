import Mathlib

theorem algebra_219676 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ (a + b) * (b + c) = 2016 ∧ (a + b) * (c + a) = 1080 ∧ x = a + b + c} 61 := by
  constructor
  · -- Show 61 is in the set. Using the solution found: a=5, b=31, c=25
    use 5, 31, 25 
    all_goals 
      norm_num
  · -- Show no element less than 61 is in the set.
    intro n hn
    rcases hn with ⟨a, b, c, ha, hb, hc, h1, h2, hn⟩
    by_contra h
    push_neg at h
    have h3 : a + b + c < 61 := by 
      omega
    have h4 : c ≥ 1 := by 
      omega
    have h5 : a + b < 60 := by 
      omega
    have h7 : (a + b) ∣ 72 := by
      have h8 : (a + b) ∣ 2016 := by
        use b + c 
        all_goals nlinarith
      have h9 : (a + b) ∣ 1080 := by
        use c + a
        all_goals nlinarith
      have h10 : (a + b) ∣ Nat.gcd 2016 1080 := by 
        apply Nat.dvd_gcd 
        · exact h8 
        · exact h9
      have h11 : Nat.gcd 2016 1080 = 72 := by 
        norm_num [Nat.gcd]
      rw [h11] at h10 
      exact h10
    interval_cases k : a + b <;> try { 
      omega 
    }
import Mathlib

theorem number_theory_23049 :
    IsLeast {b : ℕ | ∃ x : ℕ, x > 0 ∧ Nat.gcd 40 b = x + 3 ∧ Nat.lcm 40 b = x * (x + 3)} 8 := by 
  constructor
  · -- Show 8 is in the set
    use 5
    all_goals
      native_decide
  · -- Show no smaller b is in the set 
    intro b hb
    rcases hb with ⟨x, hx1, h1, h2⟩
    by_contra h 
    push_neg at h 
    have h3 : b < 8 := h
    interval_cases b <;> try { 
      simp_all [Nat.gcd, Nat.lcm]
      all_goals 
        try { 
          omega 
        }
      all_goals 
        try { 
          nlinarith 
        }
    }
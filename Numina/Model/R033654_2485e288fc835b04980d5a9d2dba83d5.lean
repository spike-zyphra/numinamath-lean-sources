import Mathlib

theorem number_theory_16288  :
  IsLeast {b | ∃ x, 0 < x ∧ (24).gcd b = x + 2 ∧ (24).lcm b = x * (x + 2)} 6 := by 
  constructor
  · -- Show that 6 is in the set with x = 4
    use 4 
    all_goals norm_num 
  · -- Show that if b in set, then b ≥ 6 
    intro b hb 
    rcases hb with ⟨x, hx1, h1, h2⟩
    by_contra h
    push_neg at h
    -- Now we have `b < 6` from `h`. We need to show this leads to a contradiction.
    -- First, compute product of gcd and lcm via known relation
    have h3 : (24 : ℕ) * b = (24).gcd b * (24).lcm b := by
      rw [Nat.gcd_mul_lcm]
    have h4 : x * (x + 2) ^ 2 = 24 * b := by
      have h_eq1 : (x + 2) * (x * (x + 2)) = 24 * b := by
        have h_eq2 : (x + 2) * (x * (x + 2)) = (Nat.gcd 24 b) * (Nat.lcm 24 b) := by 
          rw [show (Nat.gcd 24 b) = x + 2 by linarith [h1], show (Nat.lcm 24 b) = x * (x + 2) by linarith [h2]
          ]
        have h_eq3 : (Nat.gcd 24 b) * (Nat.lcm 24 b) = 24 * b := by
          rw [Nat.gcd_mul_lcm 24 b]
        linarith [h_eq2, h_eq3]
      have h_eq2 : (x + 2) * (x * (x + 2)) = x * (x + 2) ^ 2 := by 
        ring
      linarith [h_eq1, h_eq2]
    have h5 : b ≤ 5 := by 
      omega 
    interval_cases b <;> try { 
      norm_num [Nat.gcd, Nat.lcm] at h1 h2 h4 ⊢
      all_goals 
      try { 
        have h6 : x ≤ 8 := by
          nlinarith
        interval_cases x <;> omega
      }
    }
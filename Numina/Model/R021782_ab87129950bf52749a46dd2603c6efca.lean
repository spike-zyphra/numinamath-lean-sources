import Mathlib

theorem number_theory_290242 :
    IsGreatest {x | ∃ a b, x = a + b ∧ Nat.lcm a b = 140 ∧ Nat.gcd a b = 5} 145 := by 
  constructor 
  · -- Show 145 is in the set
    use 5, 140
    all_goals
    norm_num [Nat.lcm, Nat.gcd]
  · -- Show that 145 is greatest
    intro x h
    rcases h with ⟨a, b, h_eq, h1, h2⟩
    by_contra h3
    push_neg at h3
    have h4 : a.gcd b * Nat.lcm a b = a * b := by
      rw [Nat.gcd_mul_lcm a b]
    rw [h1, h2] at h4
    have h5 : a * b = 700 := by
      nlinarith
    have h6 : a + b ≤ 145 := by
      have h7 : a.gcd b = 5 := h2
      have h8 : a * b = 700 := h5
      have h37 : 5 ∣ a := by
        have h34 : a.gcd b ∣ a := Nat.gcd_dvd_left a b
        rw [h7] at h34
        exact h34
      have h38 : 5 ∣ b := by
        have h35 : a.gcd b ∣ b := Nat.gcd_dvd_right a b
        rw [h7] at h35
        exact h35
      rcases h37 with ⟨m, hm⟩
      rcases h38 with ⟨n, hn⟩
      have h39 : m.gcd n = 1 := by
        have h40 : a.gcd b = 5 := h2
        have h41 : a.gcd b = 5 * (m.gcd n) := by
          rw [show a = 5 * m by linarith [hm], show b = 5 * n by linarith [hn]]
          simp [Nat.gcd_mul_left]
        have h42 : 5 * (m.gcd n) = 5 := by
          nlinarith
        have h43 : m.gcd n = 1 := by
          omega
        exact h43
      have h42 : m * n = 28 := by
        nlinarith [h5, hm, hn]
      have h43 : m ∣ 28 := by
        use n
        all_goals
        nlinarith [h42]
      have h44 : m ≤ 28 := by
        exact Nat.le_of_dvd (by norm_num) h43
      interval_cases m <;> try { 
        omega 
      } <;> try { 
        have h45 : n ≤ 28 := by
          nlinarith
        interval_cases n <;> norm_num [Nat.gcd] at h39 h42 ⊢ 
        all_goals 
        omega
      }
    nlinarith [h_eq, h6, h3]
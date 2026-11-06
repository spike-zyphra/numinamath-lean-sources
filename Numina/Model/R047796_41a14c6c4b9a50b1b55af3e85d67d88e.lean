import Mathlib

theorem number_theory_19015 :
    IsLeast {n | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = n} 108 := by
  constructor
  · -- Show that 108 is in the set
    use 12, 54
    all_goals norm_num
  · -- Now, prove that no smaller value is possible
    intro n hn
    rcases hn with ⟨a, b, ha, hb, ha1, hb1, h1, hn⟩
    by_contra h
    push_neg at h -- Now we assume n < 108
    have h3 : 6 * n = a * b := by
      have h4 : a.gcd b * (a.lcm b) = a * b := by 
        rw [Nat.gcd_mul_lcm]
      rw [h1, hn] at h4
      linarith
    have h4 : a % 10 = 2 := by
      omega
    have h5 : b % 10 = 4 := by
      omega
    have h8 : n > 0 := by
      by_contra h
      push_neg at h
      have hn0 : n = 0 := by linarith
      rw [hn0] at h3
      have h9 : a * b = 0 := by linarith
      have h11 : a > 0 := ha
      have h12 : b > 0 := hb
      have h13 : a * b > 0 := by
        apply mul_pos
        linarith
        linarith
      linarith
      all_goals linarith
    -- Show that a and b must be divisible by 6
    have h9 : a % 3 = 0 := by
      have h6' : a.gcd b = 6 := h1
      have h10 : a % 3 = 0 := by
        have h11 : 3 ∣ a := by
          have h14 : a.gcd b = 6 := h1
          have h15 : a.gcd b ∣ a := by
            exact Nat.gcd_dvd_left a b
          rw [h14] at h15
          have h16 : 6 ∣ a := by
            exact h15
          omega
        omega
      exact h10
    -- Show that b must be divisible by 3
    have h10 : b % 3 = 0 := by
      have h6' : a.gcd b = 6 := h1
      have h11 : 3 ∣ b := by
        have h14 : a.gcd b = 6 := h1
        have h15 : a.gcd b ∣ b := by
          exact Nat.gcd_dvd_right a b
        rw [h14] at h15
        have h16 : 6 ∣ b := by
          exact h15
        omega
      omega
      all_goals omega
    -- From h3 : 6 * n = a * b and n < 108, so a * b < 648
    have h11 : a * b < 648 := by 
      nlinarith
    have h14 : a ≤ 107 := by
      by_contra h
      push_neg at h
      have h15 : b < 6 := by
        nlinarith [show b ≤ 107 by nlinarith, h]
      interval_cases b <;> try { omega }
      <;> try { 
        omega 
      }
    -- Similarly bound b
    have h15 : b ≤ 107 := by
      by_contra h
      push_neg at h
      have h16 : a < 6 := by
        nlinarith [show a ≤ 107 by nlinarith, h]
      interval_cases a <;> try { omega }
      <;> try { 
        omega 
      }
    -- Now check all possible pairs of a and b using interval_cases
    interval_cases a <;> try { 
      omega 
    } <;> interval_cases b 
      <;> norm_num [Nat.lcm, Nat.gcd] at hn h1 h3 
      <;> all_goals try { 
        omega 
      }
      <;> try { 
        exfalso 
        <;> try { 
          tauto 
        } 
      }
  all_goals try { 
    nlinarith 
  }
  <;> try { 
    tauto 
  }
  <;> try { 
    exfalso 
    <;> try { 
      tauto 
    } 
  }
  <;> try { 
    exfalso 
    <;> try { 
      all_goals try { tauto }
    } 
  }
  <;> try { 
    tauto 
  }
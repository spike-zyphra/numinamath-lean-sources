import Mathlib

theorem number_theory_610583 :
    IsLeast {x | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ∃ r : ℕ, r = Real.sqrt (a * Real.sqrt (b * Real.sqrt c)) ∧ x = a + b + c} 7 := by
  constructor
  · -- Show 7 is in the set
    use 2, 4, 1
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
    use 2
    constructor
    · -- Show that 2 = sqrt(2 * sqrt(4 * sqrt 1))
      have h1 : Real.sqrt (2 * Real.sqrt (4 * Real.sqrt (1 : ℝ))) = 2 := by
        have h2 : Real.sqrt (1 : ℝ) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h3 : Real.sqrt (4 * Real.sqrt (1 : ℝ)) = 2 := by
          rw [h2]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        have h4 : Real.sqrt (2 * Real.sqrt (4 * Real.sqrt (1 : ℝ))) = 2 := by
          rw [h3]
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        linarith
      norm_num at h1 ⊢
      all_goals try linarith
    · norm_num
  · -- Show that no integer less than 7 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hne1, hne2, hne3, r, hr, hx⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 7 := by
      omega
    have h2 : a ≤ 4 := by 
      omega
    have h3 : b ≤ 4 := by 
      omega
    have h4 : c ≤ 4 := by 
      omega
    have h3 : (Real.sqrt (a * Real.sqrt (b * Real.sqrt c))) = (Real.sqrt (a * Real.sqrt (b * Real.sqrt c))) := by rfl
    have h_eq : (r : ℝ) = Real.sqrt (a * Real.sqrt (b * Real.sqrt c)) := by
      exact_mod_cast hr
    -- Square both sides: r^2 = a * sqrt(b * sqrt c)
    have h_eq2 : (r : ℝ) ^ 2 = a * Real.sqrt (b * Real.sqrt c) := by
      calc
        (r : ℝ) ^ 2 = (Real.sqrt (a * Real.sqrt (b * Real.sqrt c))) ^ 2 := by
          rw [h_eq]
        _ = a * Real.sqrt (b * Real.sqrt c) := by
          have h3 : Real.sqrt (a * Real.sqrt (b * Real.sqrt c)) ^ 2 = a * Real.sqrt (b * Real.sqrt c) := by
            apply Real.sq_sqrt
            positivity
          linarith
    have h_eq3 : (Real.sqrt (b * Real.sqrt c)) ^ 2 = b * Real.sqrt c := by
      apply Real.sq_sqrt
      positivity
    have h_eq4 : (Real.sqrt c) ^ 2 = (c : ℝ) := by
      rw [Real.sq_sqrt]
      exact_mod_cast (show (0 : ℝ) ≤ (c : ℝ) by positivity)
    -- Square again: r^4 = a^2 b * sqrt c
    have eq1 : (r : ℝ) ^ 4 = a^2 * b * Real.sqrt c := by
      calc
        (r : ℝ) ^ 4 = ((r : ℝ) ^ 2) ^ 2 := by ring
        _ = (a * Real.sqrt (b * Real.sqrt c)) ^ 2 := by
          rw [h_eq2]
        _ = a^2 * (Real.sqrt (b * Real.sqrt c)) ^ 2 := by ring
        _ = a^2 * (b * Real.sqrt c) := by
          rw [h_eq3]
        _ = a^2 * b * Real.sqrt c := by 
          ring
    -- Square again: r^8 = a^4 b^2 c
    have eq2 : (r : ℝ) ^ 8 = a^4 * b^2 * (c : ℝ) := by
      calc
        (r : ℝ) ^ 8 = ((r : ℝ) ^ 4) ^ 2 := by ring
        _ = (a^2 * b * Real.sqrt c) ^ 2 := by
          rw [eq1]
        _ = (a^2 * b) ^ 2 * (Real.sqrt c) ^ 2 := by
          ring
        _ = (a^2 * b) ^ 2 * (c : ℝ) := by
          rw [h_eq4]
        _ = a^4 * b^2 * (c : ℝ) := by
          ring_nf
    have eq3 : (r : ℝ) ^ 8 = a^4 * b^2 * (c : ℝ) := by
      linarith [eq2]
    have hr1 : r ^ 8 = a^4 * b^2 * c := by
      have h10 : (r : ℝ) ^ 8 = (a^4 * b^2 * (c : ℝ) : ℝ) := by
        nlinarith [eq2]
      have h11 : (r ^ 8 : ℝ) = (a^4 * b^2 * c : ℝ) := by
        norm_num at h10 ⊢
        norm_cast at h10 ⊢
        <;> nlinarith
      norm_cast at h11 ⊢ 
      <;> nlinarith
    interval_cases a <;> interval_cases b
    <;> interval_cases c
    <;> try { 
      omega 
    }
    <;> try { 
      norm_num at *
      all_goals
      try { 
        have h2 : r ≤ 7 := by
          have : r ^ 8 ≤ (7 : ℕ) ^ 8 := by nlinarith
          have h4 : r ≤ 7 := by
            by_contra h
            push_neg at h
            have h5 : r ^ 8 ≥ 8 ^ 8 := by
              have h6 : r ≥ 8 := by
                omega
              have h7 : r ^ 8 ≥ (8 : ℕ) ^ 8 := by
                apply Nat.pow_le_pow_of_le_left
                omega
              omega
            nlinarith
          omega
        interval_cases r <;> omega 
      }
    }
    <;> try { 
      omega 
    }
    <;> try { 
      all_goals
      try { 
        exfalso
        <;> try { 
          linarith 
        }
        <;> try { 
          nlinarith 
        }
      }
    }
    <;> try { 
      all_goals
      try { 
        interval_cases r 
        <;> omega 
      }
    }
    <;> try { 
      all_goals 
      try { 
        nlinarith 
      }
    }
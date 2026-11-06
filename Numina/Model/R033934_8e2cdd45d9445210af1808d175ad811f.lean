import Mathlib

theorem algebra_15716 : IsGreatest {Nat.ofDigits 10 [c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (ha : a ∈ Finset.Icc 1 9) (hb : b ∈ Finset.Icc 0 9) (hc : c ∈ Finset.Icc 0 9) (h_dist : a ≠ b ∧ b ≠ c ∧ a ≠ c) (h_geom : ∃ q : ℚ, q ≠ 0 ∧ b = a * q ∧ c = b * q)} 964 := by 
  constructor 
  · -- Show 964 is in the set 
    use 9, 6, 4
    simp [Nat.ofDigits, Finset.mem_Icc]
    <;> norm_num 
    <;> use (2 / 3 : ℚ) <;> norm_num
  · -- Show no greater element is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_dist, h_geom, hx⟩
    simp [Nat.ofDigits] at hx ⊢
    rcases h_geom with ⟨q, hq0, hpart1, hpart2⟩ 
    rw [Finset.mem_Icc] at ha hb hc
    rcases h_dist with ⟨ha1, hb1, hc1⟩ 
    by_contra h 
    push_neg at h 
    -- Show a contradiction
    have h0 : 100 * a + 10 * b + c > 964 := by 
      omega 
    -- From the geometric progression constraints
    have eq1 : (b : ℚ) = (a : ℚ) * q := by 
      linarith 
    have eq2 : (c : ℚ) = (b : ℚ) * q := by 
      linarith 
    have eq3 : (c : ℚ) = (a : ℚ) * q ^ 2 := by 
      rw [eq2, eq1]
      ring 
    have h_eq1 : (b : ℚ) ^ 2 = (a : ℚ) * (c : ℚ) := by 
      have eq1' : (c : ℚ) = (a : ℚ) * q ^ 2 := eq3
      have eq2' : (b : ℚ) = (a : ℚ) * q := eq1
      rw [show (b : ℚ) = (a : ℚ) * q by linarith [eq1]]
      rw [show (c : ℚ) = (a : ℚ) * q ^ 2 by linarith [eq3]]
      ring_nf 
    have h_eq2 : b ^ 2 = a * c := by
      exact_mod_cast h_eq1 
    have h4 : a ≤ 9 := by 
      omega 
    have h5 : b ≤ 9 := by 
      omega 
    have h6 : c ≤ 9 := by 
      omega 
    interval_cases a <;> 
      try { 
        omega 
      } 
      <;> 
        interval_cases b <;> 
          try { 
            omega 
          } 
          <;> 
            try { 
              interval_cases c <;> 
                try { 
                  norm_num at h_eq2 h0 
                  <;> 
                    omega 
                }
            }
import Mathlib

def D (a n : ℕ) := ∑ i ∈ Finset.range n, a * 2 ^ i

theorem algebra_110553 :
    IsLeast {n | 0 < n ∧ ∀ i ∈ Finset.Icc 1 6, ∃ a, 0 < a ∧ D a i = n} 9765 := by
  constructor
  · -- Show 9765 is in the set
    constructor
    · norm_num
    · intro i hi
      have h1 : i ≥ 1 := by
        have h2 : i ∈ Finset.Icc 1 6 := hi
        simp at h2 ⊢
        omega
      have h3 : i ≤ 6 := by 
        have h4 : i ∈ Finset.Icc 1 6 := hi
        simp at h4 ⊢
        omega
      interval_cases i <;> try {
        use 9765 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
      <;> try { 
        use 3255 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
      <;> try { 
        use 1395 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
      <;> try { 
        use 651 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
      <;> try { 
        use 315 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
      <;> try { 
        use 155 
        all_goals norm_num [D, Finset.sum_range_succ] 
      }
  · -- Show no number less than 9765 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_prop⟩
    by_contra h
    push_neg at h
    have h1 := hn_prop 6 (by norm_num)
    rcases h1 with ⟨a, ha_pos, ha_eq⟩
    have h4 : D a 6 = n := by linarith
    simp [D, Finset.sum_range_succ] at h4
    have h5 : n = 63 * a := by 
      omega
    have h6 : n > 0 := hn_pos
    have h7 : a > 0 := ha_pos
    have h8 := hn_prop 5 (by norm_num)
    rcases h8 with ⟨b, hb_pos, hb_eq⟩
    have h8 : D b 5 = n := by linarith
    simp [D, Finset.sum_range_succ] at h8
    have h9 : n = 31 * b := by 
      omega
    have h10 : 31 ∣ 63 * a := by 
      omega
    have h11 : 31 ∣ a := by 
      omega
    have h12 := hn_prop 4 (by norm_num)
    rcases h12 with ⟨c, hc_pos, hc_eq⟩
    have h13 : D c 4 = n := by linarith
    simp [D, Finset.sum_range_succ] at h13
    have h14 : n = 15 * c := by 
      omega
    have h3 := hn_prop 3 (by norm_num)
    rcases h3 with ⟨d, hd_pos, hd_eq⟩
    have h14 : D d 3 = n := by linarith
    simp [D, Finset.sum_range_succ] at h14
    have h15 : n = 7 * d := by 
      omega
    have h2 := hn_prop 2 (by norm_num)
    rcases h2 with ⟨e, he_pos, he_eq⟩
    have h15 : D e 2 = n := by linarith
    simp [D, Finset.sum_range_succ] at h15
    have h16 : n = 3 * e := by 
      omega
    have h11 := hn_prop 1 (by norm_num)
    rcases h11 with ⟨f, hf_pos, hf_eq⟩
    have h16 : D f 1 = n := by linarith
    simp [D, Finset.sum_range_succ] at h16
    have h17 : n = f := by 
      omega
    -- Now we have multiple equations:
    -- n = 63 * a
    -- n = 31 * b
    -- n = 15 * c
    -- n = 7 * d
    -- n = 3 * e
    -- n = f
    -- and n < 9765
    -- We need to show that this leads to a contradiction
    have h18 : n < 9765 := h
    -- We will use the constraints to find a contradiction
    -- n must be a multiple of 9765, so n < 9765 contradicts since 9765 is the LCM
    -- Let Lean's omega solve the arithmetic
    omega
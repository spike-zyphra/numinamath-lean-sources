import Mathlib

theorem number_theory_213434 :
    IsGreatest {n | n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧ (Nat.digits 10 n).toFinset.card = 4 ∧ 2 ∣ n ∧ 5 ∣ n ∧ 9 ∣ n ∧ 11 ∣ n} 8910 := by
  constructor
  · -- First, show 8910 is in the set
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Then, show no number greater than 8910 is in the set
    intro n hn
    rcases hn with ⟨hn1, hn2, hn3, hn4, hn5, hn6, hn7⟩
    rw [Finset.mem_Icc] at hn1
    rcases hn1 with ⟨hn1_lower, hn1_upper⟩
    by_contra h
    push_neg at h
    have h1 : n ≤ 9999 := hn1_upper
    have h2 : n > 8910 := h
    have h3 : n = 9900 := by
      have h990 : 990 ∣ n := by 
        have h2 : 2 ∣ n := hn4
        have h5 : 5 ∣ n := hn5
        have h9 : 9 ∣ n := hn6
        have h11 : 11 ∣ n := hn7
        have h_2_5 : Nat.Coprime 2 5 := by norm_num
        have h_2_9 : Nat.Coprime 2 9 := by norm_num
        have h_2_11 : Nat.Coprime 2 11 := by norm_num
        have h_5_9 : Nat.Coprime 5 9 := by norm_num
        have h_5_11 : Nat.Coprime 5 11 := by norm_num
        have h_9_11 : Nat.Coprime 9 11 := by norm_num
        have h10 : 10 ∣ n := by
          have h2' : n % 2 = 0 := by omega
          have h5' : n % 5 = 0 := by omega
          omega
        have h90 : 90 ∣ n := by
          have h10' : 10 ∣ n := h10
          have h9' : 9 ∣ n := h9
          have h10_9 : Nat.Coprime 10 9 := by norm_num
          exact Nat.lcm_dvd h10' h9'
        have h990 : 990 ∣ n := by
          have h90' : 90 ∣ n := h90
          have h11' : 11 ∣ n := h11
          have h90_11 : Nat.Coprime 90 11 := by norm_num
          exact Nat.lcm_dvd h90' h11'
        exact h990
      omega
    rw [h3] at hn3
    norm_num at hn3

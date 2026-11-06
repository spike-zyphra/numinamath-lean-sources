import Mathlib

theorem number_theory_11379 :
    IsLeast {x | ∃ k l : ℕ, k ∈ Set.Icc 1000 9999 ∧ l ∈ Set.Icc 1000 9999 ∧ Nat.gcd k l = 3 ∧ x = Nat.lcm k l} 335670 := by
  constructor
  · -- Show that 335670 is in the set
    use 1002, 1005
    constructor
    · -- Show 1002 ∈ [1000, 9999]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 1005 ∈ [1000, 9999]
      exact Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show gcd(1002, 1005) = 3
      norm_num [Nat.gcd]
    · -- Show 335670 = lcm(1002, 1005)
      norm_num [Nat.lcm]
  · -- Show that 335670 is the least element
    intro x hx
    rcases hx with ⟨k, l, hk, hl, h1, h2⟩
    rw [Set.mem_Icc] at hk hl
    rcases hk with ⟨hk1, hk2⟩
    rcases hl with  ⟨hl1, hl2⟩
    by_contra h
    push_neg at h
    have h3 : Nat.gcd k l = 3 := h1
    have h4 : x = Nat.lcm k l := h2
    have h5 : Nat.lcm k l < 335670 := by linarith
    have h12 : k * l = 3 * (Nat.lcm k l) := by
      have h13 : k * l = (Nat.gcd k l) * (Nat.lcm k l) := by
        rw [Nat.gcd_mul_lcm]
      rw [h1] at h13
      omega
    have h13 : k * l < 1007010 := by
      nlinarith [h5, h12, show l ≥ 1000 by linarith, show k ≥ 1000 by linarith]
    have h14 : k ≤ 1007 := by
      nlinarith [show l ≥ 1000 by linarith]
    have h15 : l ≤ 1007 := by
      nlinarith [show k ≥ 1000 by linarith]
    interval_cases k <;> try { omega } <;> try { 
      interval_cases l 
      <;> norm_num [Nat.gcd, Nat.lcm] at h1 h5 h12 h13 ⊢ 
      <;> all_goals omega 
    }
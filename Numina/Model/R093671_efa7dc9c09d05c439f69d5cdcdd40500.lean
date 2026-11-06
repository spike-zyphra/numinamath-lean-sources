import Mathlib

theorem algebra_12965 :
    IsLeast {n | 0 < n ∧ ∃ k, n = k^2 ∧ 2 ∣ n ∧ 3 ∣ n} 36 := by 
  constructor
  · -- Show 36 is in the set
    constructor
    · norm_num
    · -- Establish that 36 = 6² and check divisibility
      use 6
      all_goals norm_num
  · -- Show there is no smaller number in the set
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, rfl, hk1, hk2⟩⟩
    -- Assume n is in the set, so there exists k such that n = k^2, 2 divides n, 3 divides n
    have h2 : 2 ∣ k := by
      have h6' : k ^ 2 % 2 = 0 := by 
        omega
      have : k % 2 = 0 := by
        by_contra h
        push_neg at h
        have : k % 2 = 1 := by 
          omega
        have h' : k ^ 2 % 2 = 1 := by 
          simp [Nat.pow_mod, this]
        omega
      omega
    have h3 : 3 ∣ k := by
      have h3'' : k ^ 2 % 3 = 0 := by 
        omega
      have : k % 3 = 0 := by
        by_contra h
        push_neg at h
        have : k % 3 = 1 ∨ k % 3 = 2 := by 
          omega
        rcases this with (h | h)
        · -- k ≡ 1 (mod 3) then k^2 ≡ 1 (mod 3)
          have : k ^ 2 % 3 = 1 := by 
            simp [Nat.pow_mod, h]
          omega
        · -- k ≡ 2 (mod 3) then k^2 ≡ 4 ≡ 1 (mod 3)
          have : k ^ 2 % 3 = 1 := by 
            simp [Nat.pow_mod, h]
          omega
      omega
    have h6 : 6 ∣ k := by 
      omega
    have eq : k ≥ 6 := by
      by_contra h
      push_neg at h
      have h6' : k < 6 := by
        omega
      have h1 : k ≤ 5 := by
        omega
      interval_cases k <;> try { contradiction } <;> norm_num at hk1 hk2 <;> omega
    nlinarith [show k ≥ 6 from by linarith]
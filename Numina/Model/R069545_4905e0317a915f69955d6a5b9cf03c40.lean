import Mathlib

theorem number_theory_4047 : IsLeast {x : ℕ | x ∈ Finset.Icc 10000 99999 ∧ x % 11 = 4 ∧ x % 13 = 6 ∧ x % 17 = 8} 10718 := by 
  constructor
  · -- Show that 10718 belongs to the set.
    constructor
    · -- Show it's a 5-digit number
      simp [Finset.mem_Icc]
    constructor
    · -- Check remainder modulo 11 is 4
      norm_num
    constructor
    · -- Check remainder modulo 13 is 6
      norm_num
    · -- Check remainder modulo 17 is 8
      norm_num
  · -- Show that 10718 is the smallest such number
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    rw [Finset.mem_Icc] at hx1
    rcases hx1 with ⟨hx11, hx12⟩
    -- Now x is in the range [10000, 99999] and satisfies the congruences. We need to prove x >= 10718
    by_contra h
    push_neg at h
    have h1 : x < 10718 := by omega
    interval_cases x <;> omega
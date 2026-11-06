import Mathlib

theorem number_theory_2898 : IsLeast {x | x ∈ Finset.Icc 1000 9999 ∧ x % 7 = 2 ∧ x % 11 = 7 ∧ x % 13 = 4} 1668 := by
  constructor
  · -- Verify 1668 is in the set
    constructor
    · -- Show 1668 is in the range [1000, 9999]
      simp [Finset.mem_Icc]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show no smaller element is in the set
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    rw [Finset.mem_Icc] at hx1
    rcases hx1 with ⟨hx1l, hx1u⟩
    by_contra h
    push_neg at h
    interval_cases x <;> omega
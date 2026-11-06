import Mathlib

theorem number_theory_43996 :
    IsLeast {N | 0 < N ∧ 19 ∣ N ∧ (Nat.digits 10 N).sum = 23} 779 := by
  constructor
  · -- First, we prove that 779 belongs to the set
    refine' ⟨by norm_num, by norm_num, by norm_num [Nat.digits, Nat.digitsAux]⟩
  · -- Then, we prove that 779 is the smallest
    intro N h
    have ⟨hN_pos, hN_div, hSum⟩ := h
    by_contra h'
    push_neg at h'
    interval_cases N <;> norm_num at hN_div hSum <;> all_goals
      try { contradiction }
      <;> omega
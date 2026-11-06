import Mathlib

theorem number_theory_3021 : IsGreatest {N | N ∈ Finset.Icc 1000 9999 ∧ N % 17 = 5 ∧ N % 18 = 7} 9763 := by
  constructor
  · -- Show that 9763 is in the set
    refine ⟨by norm_num [Finset.mem_Icc], by norm_num, by norm_num⟩
  
  · -- Show that 9763 is the greatest
    intro N hN
    have h1 : N ∈ Finset.Icc 1000 9999 := hN.left
    have h2 : N % 17 = 5 := hN.right.left
    have h3 : N % 18 = 7 := hN.right.right

    rw [Finset.mem_Icc] at h1
    obtain ⟨hN1, hN2⟩ := h1

    by_contra h
    push_neg at h

    interval_cases N <;> norm_num at h2 h3 <;> omega
import Mathlib

theorem number_theory_238395: IsGreatest {a1: ℤ | ∃ a2 a3 a4 a5 a6 a7 a8 a9 a10 : ℤ,
  0 ≤ a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧ a8 < a9 ∧ a9 < a10 ∧
  (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) / (10: ℚ) = 12.5} 8 := by
  constructor
  · -- Show that 8 is in the set
    simp only [Set.mem_setOf_eq]
    use 9, 10, 11, 12, 13, 14, 15, 16, 17
    norm_num
  · -- Show that any element in the set is at most 8
    intro a1 h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨a2, a3, a4, a5, a6, a7, a8, a9, a10, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    by_contra h
    push_neg at h
    have h11 : a1 ≥ 9 := by omega
    have h12 : a2 ≥ a1 + 1 := by omega
    have h13 : a3 ≥ a2 + 1 := by omega
    have h14 : a4 ≥ a3 + 1 := by omega
    have h15 : a5 ≥ a4 + 1 := by omega
    have h16 : a6 ≥ a5 + 1 := by omega
    have h17 : a7 ≥ a6 + 1 := by omega
    have h18 : a8 ≥ a7 + 1 := by omega
    have h19 : a9 ≥ a8 + 1 := by omega
    have h20 : a10 ≥ a9 + 1 := by omega
    have h13 : a2 ≥ 10 := by omega
    have h14 : a3 ≥ 11 := by omega
    have h15 : a4 ≥ 12 := by omega
    have h16 : a5 ≥ 13 := by omega
    have h17 : a6 ≥ 14 := by omega
    have h18 : a7 ≥ 15 := by omega
    have h19 : a8 ≥ 16 := by omega
    have h20 : a9 ≥ 17 := by omega
    have h21 : a10 ≥ 18 := by omega
    have h125 : (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) = 125 := by
      have h10' : (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10) / (10 : ℚ) = 12.5 := h10
      have h126 : (a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 : ℚ) = 125 := by
        field_simp at h10'
        linarith
      exact_mod_cast h126
    have h22 : a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 ≥ 135 := by
      omega
    linarith
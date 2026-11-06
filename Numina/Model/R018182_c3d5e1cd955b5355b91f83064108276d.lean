import Mathlib

theorem number_theory_5303 : IsGreatest {x | Odd x ∧ x ∈ Finset.Icc 100 999 ∧ x ≡ 17 [ZMOD 23]} 983 := by
  constructor
  · -- Show 983 is in the set.
    constructor
    · -- 983 is odd
      exact Int.odd_iff.mpr (by norm_num)
    constructor
    · -- Show 983 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 983 ≡ 17 [ZMOD 23]
      native_decide
  · -- Show that for all x in the set, x ≤ 983
    intro x hx
    rcases hx with ⟨hx_odd, hx_range, hx_mod⟩
    rw [Finset.mem_Icc] at hx_range
    rcases hx_range with ⟨hx1, hx2⟩
    by_contra h
    push_neg at h
    have h4 : x % 23 = 17 := by 
      norm_num [Int.ModEq] at hx_mod ⊢
      omega
    have h5 : x > 983 := h
    have h6 : x ≤ 999 := by linarith
    interval_cases x <;> norm_num at h4 h5 h6 hx_odd <;> norm_num [Int.ModEq] at hx_mod <;> try { contradiction }
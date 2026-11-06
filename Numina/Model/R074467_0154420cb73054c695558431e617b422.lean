import Mathlib

theorem number_theory_9583 : IsGreatest {x | x ∈ Finset.Icc 1000 9999 ∧ x ≡ 19 [ZMOD 23] ∧ x ≡ 19 [ZMOD 29]} 9357 := by
  constructor
  · -- Show 9357 is in the set
    constructor
    · exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 9357 ≡ 19 [MOD 23]
      norm_num [Int.ModEq]
    · -- Show 9357 ≡ 19 [MOD 29]
      norm_num [Int.ModEq]
  · -- Show that 9357 is greatest in the set
    intro x hx
    rcases hx with ⟨hx1, hx2, hx3⟩
    rw [Finset.mem_Icc] at hx1
    rcases hx1 with ⟨h1, h2⟩
    by_contra h
    push_neg at h
    norm_num [Int.ModEq] at hx2 hx3
    interval_cases x <;> omega
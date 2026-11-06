import Mathlib

theorem number_theory_19339 : IsGreatest {x | x < 0 ∧ 24 * x ≡ 15 [ZMOD 1199]} (-449) := by
  constructor
  · constructor
    · norm_num
    · norm_num [Int.ModEq]
  · intro y hy
    have ⟨hy1, hy2⟩ := hy
    by_contra h
    push_neg at h
    have h1 : y ≥ -448 := by omega
    interval_cases y <;> norm_num [Int.ModEq] at hy2 <;> omega
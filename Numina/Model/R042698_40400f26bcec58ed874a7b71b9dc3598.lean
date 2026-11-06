import Mathlib
theorem number_theory_22983 :
    IsGreatest {x | 17 ∣ x ∧ x < 1000 ∧ (x + 1) % 8 = 0} 935 := by
  constructor
  · -- Show that 935 is in the set.
    show 17 ∣ 935 ∧ 935 < 1000 ∧ (935 + 1) % 8 = 0
    constructor
    · norm_num -- 935 is a multiple of 17
    constructor
    · norm_num -- 935 is less than 1000
    · norm_num -- (935 + 1) % 8 = 0
  · -- Show that no greater element is in the set
    intro y hy
    rcases hy with ⟨h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : y ≥ 936 := by
      omega
    have h5 : y % 8 = 7 := by
      omega
    omega
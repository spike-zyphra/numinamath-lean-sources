import Mathlib

theorem algebra_1413 : {n : ℕ | n > 0 ∧ 3^2 + 4^2 + 12^2 = n^2} = {13} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, suppose n is in the leftset, so n > 0 and 3^2+4^2+12^2 = n^2, prove n = 13
    intro h
    rcases h with ⟨hn_pos, heq⟩
    have h1 : n ≤ 13 := by
      nlinarith
    have h2 : n ≥ 13 := by
      by_contra h
      push_neg at h
      have h3 : n ≤ 12 := by
        omega
      nlinarith
    have heq_n : n = 13 := by
      omega
    exact heq_n
  · -- Now prove the reverse, if n = 13, then it's in the leftset
    intro heq_n
    rw [heq_n]
    constructor
    · norm_num
    all_goals norm_num
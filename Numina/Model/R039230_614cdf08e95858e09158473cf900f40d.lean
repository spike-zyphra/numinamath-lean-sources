import Mathlib

theorem algebra_289745 :
  {v : ℝ | v > 0 ∧ v ≠ 16 ∧ 31 / (v + 16) = 15 / (v - 16)} = {46} := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume v is in the set {v | v > 0 ∧ v ≠ 16 ∧ 31 / (v + 16) = 15 / (v - 16)}
    intro h
    rcases h with ⟨hv_pos, hv_ne, heq⟩
    have h1 : v + 16 ≠ 0 := by
      linarith
    have h2 : v - 16 ≠ 0 := by
      intro h3
      apply hv_ne
      linarith
    field_simp [h1, h2] at heq
    nlinarith
  · -- Assume v = 46 and prove that v ∈ {v > 0 ∧ v ≠ 16 ∧ 31 / (v + 16) = 15 / (v - 16)}
    intro h
    rw [h]
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
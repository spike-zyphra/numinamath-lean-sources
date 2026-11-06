import Mathlib

theorem algebra_286616 :
  {ρ : ℝ | ρ > 0 ∧ ρ - 1/2 = 2 * (ρ - 1)} = {1.5} := by
  ext ρ
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume h1: ρ > 0 and h2: ρ - 1/2 = 2 * (ρ - 1)
    rintro ⟨h1, h2⟩
    have h3 : ρ = (3 : ℝ) / 2 := by
      linarith
    rw [h3]
    norm_num
  · -- Assume h: ρ = 1.5
    intro h
    rw [h]
    constructor
    · norm_num
    · norm_num
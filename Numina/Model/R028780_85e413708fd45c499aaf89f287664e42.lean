import Mathlib

theorem number_theory_610843 :
    {m : ℕ | ∃ a₂ a₃ a₄ a₅ n : ℕ, a₂ ≤ 9 ∧ a₃ ≤ 9 ∧ a₄ ≤ 9 ∧ a₅ ≤ 9 ∧ Even n ∧ m = n * (n + 2) * (n + 4) ∧ m = 200000 + a₂ * 10000 + a₃ * 1000 + a₄ * 100 + a₅ * 10 + 2} = {287232} := by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First direction: if m in the left side, must be 287232
    rintro ⟨a₂, a₃, a₄, a₅, n, ha₂, ha₃, ha₄, ha₅, heven, h₁, h₂⟩
    rw [h₂] at h₁
    have h3 : n ≤ 80 := by
      by_contra h
      push_neg at h
      have h6 : n * (n + 2) * (n + 4) ≥ 80 * 82 * 84 := by
        have h7 : n ≥ 80 := by omega
        have h8 : n + 2 ≥ 82 := by omega
        have h9 : n + 4 ≥ 84 := by omega
        have h10 : n * (n + 2) * (n + 4) ≥ 80 * 82 * 84 := by
          apply Nat.mul_le_mul
          apply Nat.mul_le_mul
          all_goals linarith
        linarith
      nlinarith [h6, h₁, ha₂, ha₃, ha₄, ha₅]
    interval_cases n <;> try { 
      simp [Nat.even_iff] at heven h₁ 
      <;> omega 
    }
  · -- Second direction. Assume m = 287232 must be in the left side.
    intro h
    rw [h]
    use 8, 7, 2, 3, 64
    all_goals
      norm_num [Nat.even_iff]
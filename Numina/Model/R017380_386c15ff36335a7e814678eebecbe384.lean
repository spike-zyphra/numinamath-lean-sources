import Mathlib

theorem algebra_171373 : {a : ℕ | ∃ b : ℕ, 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 3 * a + b = 333}.encard = 23 := by
  have h1 : {a : ℕ | ∃ b : ℕ, 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 3 * a + b = 333} = Set.Icc 78 100 := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume ∃ b, 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 3 * a + b = 333, prove 78 ≤ a ∧ a ≤ 100
      intro h
      rcases h with ⟨b, ha1, ha2, hb1, hb2, heq⟩
      omega
    · -- Assume 78 ≤ a ∧ a ≤ 100, prove ∃ b, 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 3 * a + b = 333
      rintro ⟨ha1, ha2⟩
      use 333 - 3 * a
      omega
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { native_decide }
  <;> try { omega }
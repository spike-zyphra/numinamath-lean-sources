import Mathlib

theorem inequalities_5933 : {x : ℕ | x > 0 ∧ x ^ 2 < 14 * x + 392}.encard = 27 := by
  have h1 : {x : ℕ | x > 0 ∧ x ^ 2 < 14 * x + 392} = Set.Icc 1 27 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ≤ 27 := by
        by_contra h
        push_neg at h
        have h3 : x ≥ 28 := by omega
        have h4 : x ^ 2 ≥ 14 * x + 392 := by
          nlinarith [sq_nonneg (x - 28 : ℤ), sq_nonneg (x : ℤ)]
        linarith
      omega
    · rintro ⟨h1, h2⟩
      constructor
      · omega
      · nlinarith
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> try rfl
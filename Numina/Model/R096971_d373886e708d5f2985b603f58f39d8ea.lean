import Mathlib

theorem inequalities_6568 :
    Set.ncard {x : ℤ | -56 ≤ 5 * x + 14 ∧ 5 * x + 14 < 89} = 29 := by
  have h1 : {x : ℤ | -56 ≤ 5 * x + 14 ∧ 5 * x + 14 < 89} = Set.Icc (-14) 14 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume $-56 \leq 5x + 14 \wedge 5x + 14 < 89$, prove $-14 \leq x \wedge x \leq 14$
      rintro ⟨h₁, h₂⟩
      constructor
      · -- Solving $-56 \leq 5x + 14$ for $x$.
        linarith
      · -- Solving $5x + 14 < 89$ for $x$.
        linarith
    · -- Assume $-14 \leq x \wedge x \leq 14$, prove $-56 \leq 5x + 14 \wedge 5x + 14 < 89$
      rintro ⟨h₁, h₂⟩
      constructor
      · -- Solving $x \geq -14$ implies $5x + 14 \geq -56$.
        linarith
      · -- Solving $x < 15$ implies $5x + 14 < 89$.
        linarith
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Int.card_Icc]
  <;> try native_decide
import Mathlib

theorem inequalities_6539 : {x : ℤ | -4 ≤ (2 * (x - 1)) / 5 ∧ (2 * (x - 1)) / 5 < 6}.ncard = 25 := by
  have h1 : {x : ℤ | -4 ≤ (2 * (x - 1)) / 5 ∧ (2 * (x - 1)) / 5 < 6} = Set.Icc (-9 : ℤ) (15 : ℤ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume $x$ is in the set
      intro h
      rcases h with ⟨h1, h2⟩
      constructor
      · -- Show that $x \geq -9$
        omega
      · -- Show that $x \leq 15$
        omega
    · -- Assume $x$ is in the interval
      rintro ⟨h1, h2⟩
      constructor
      · -- Show that $-4 \leq (2 * (x - 1)) / 5$
        omega
      · -- Show that $(2 * (x - 1)) / 5 < 6$
        omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide
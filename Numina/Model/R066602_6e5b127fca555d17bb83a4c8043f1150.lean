import Mathlib

theorem algebra_97827 (a : Fin 10 → ℝ) (ha : a 0 = 6 ∧ a 1 = 19 ∧ a 2 = 33 ∧ a 3 = 33 ∧ a 4 = 39 ∧ a 5 = 41 ∧ a 6 = 41 ∧ a 7 = 43 ∧ a 8 = 51 ∧ a 9 = 57)
    (Q1 Q2 Q3 : ℝ) (hQ1 : Q1 = 33) (hQ2 : Q2 = 40) (hQ3 : Q3 = 43) :
    {x | x ∈ Set.range a ∧ (x < Q1 - 1.5 * (Q3 - Q1) ∨ x > Q3 + 1.5 * (Q3 - Q1))}.encard = 1 := by 
  rcases ha with ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9⟩
  have h1 : {x | x ∈ Set.range a ∧ (x < Q1 - 1.5 * (Q3 - Q1) ∨ x > Q3 + 1.5 * (Q3 - Q1))} = {6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Set.mem_range]
    constructor
    · -- Assume x is in the set, then either x < 18 or x > 58
      rintro ⟨hx, h⟩
      rcases h with h1 | h2
      · -- Case where x < Q1 - 1.5 * (Q3 - Q1)
        rcases hx with ⟨i, hi⟩
        fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at hi <;> norm_num [hQ1, hQ3] at h1 ⊢ <;> linarith [hi]
      · -- Case where x > Q3 + 1.5 * (Q3 - Q1)
        rcases hx with ⟨i, hi⟩
        fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9] at hi <;> norm_num [hQ1, hQ3] at h2 ⊢ <;> linarith [hi]
    · -- Assume x = 6, prove x is in the set
      intro hx
      rw [hx]
      constructor
      · -- Show 6 is in the range of a
        simpa using ⟨0, by simp [ha0]⟩
      · -- Show 6 < 18
        norm_num [hQ1, hQ3]
  rw [h1]
  simp [Set.encard_singleton]
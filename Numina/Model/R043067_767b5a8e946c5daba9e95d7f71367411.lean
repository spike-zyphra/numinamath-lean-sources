import Mathlib

theorem algebra_262311 :
  {(a, d) : ℚ × ℚ | ∀ n : ℕ, ∑ i in Finset.range n, (a + d * i) = n ^ 2 / 2} =
  {(1/2, 1)} := by
  ext ⟨a, d⟩
  simp
  constructor
  · -- First, prove the forward direction: if the pair is in the set, it equals (1/2, 1)
    intro h
    have eq1 := h 1
    norm_num [Finset.sum_range_succ] at eq1
    have eq2 := h 2
    norm_num [Finset.sum_range_succ] at eq2
    have eq3 := h 3
    norm_num [Finset.sum_range_succ] at eq3
    have eq4 : a = 1 / 2 := by
      linarith
    have eq5 : d = 1 := by
      rw [eq4] at eq2
      linarith
    simp [eq4, eq5]
  · -- Now the reverse direction: if the pair is (1/2, 1), then it satisfies the condition
    rintro ⟨rfl, rfl⟩
    intro n
    have h1 : ∀ (n : ℕ), ∑ i in Finset.range n, (1 / 2 + (1 : ℚ) * i) = (n : ℚ) ^ 2 / 2 := by 
      intro n 
      induction n with 
      | zero => 
        simp 
      | succ n ih => 
        rw [Finset.sum_range_succ, ih]
        all_goals 
          field_simp at *
          <;> ring
    specialize h1 n 
    simpa using h1
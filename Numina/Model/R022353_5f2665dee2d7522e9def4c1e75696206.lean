import Mathlib

theorem inequalities_240912 (x : Fin 5 → ℕ) (h : ∀ i, x i ≤ 100)
    (h' : ∑ i, x i = 87 * 5) :
    ∀ i, x i ≥ 35 := by
  intro i
  have h2 : ∑ j, x j = 435 := by 
    norm_num [h'] 
  have h3 : x 0 ≤ 100 := h 0
  have h4 : x 1 ≤ 100 := h 1
  have h5 : x 2 ≤ 100 := h 2
  have h6 : x 3 ≤ 100 := h 3
  have h7 : x 4 ≤ 100 := h 4
  have eq1 : x 0 + x 1 + x 2 + x 3 + x 4 = 435 := by
    have eq2 : ∑ j, x j = x 0 + x 1 + x 2 + x 3 + x 4 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      <;> ring
    rw [eq2] at h2
    omega
  have h8 : x i ≥ 35 := by
    by_contra h9
    push_neg at h9
    have h10 : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
      fin_cases i <;> simp
    rcases h10 with (rfl | rfl | rfl | rfl | rfl)
    · -- Case i = 0
      have h9' : x 0 ≤ 34 := by 
        omega
      omega
    · -- Case i = 1
      have h9' : x 1 ≤ 34 := by 
        omega
      omega
    · -- Case i = 2
      have h9' : x 2 ≤ 34 := by 
        omega
      omega
    · -- Case i = 3
      have h9' : x 3 ≤ 34 := by 
        omega
      omega
    · -- Case i = 4
      have h9' : x 4 ≤ 34 := by 
        omega
      omega
  exact h8
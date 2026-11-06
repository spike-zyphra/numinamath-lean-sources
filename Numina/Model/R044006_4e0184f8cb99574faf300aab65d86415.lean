import Mathlib

theorem algebra_20750 : IsLeast {x | ∃ (a : Fin 5 → ℝ) (ha : ∀ i, a i ∈ Set.Icc 0 100) (h : ∑ i, a i = 440), ∃ i, a i = x} 40 := by
  constructor
  · -- Show 40 is in the set.
    use fun i =>
      match i with
      | 0 => (40 : ℝ)
      | 1 => (100 : ℝ)
      | 2 => (100 : ℝ)
      | 3 => (100 : ℝ)
      | 4 => (100 : ℝ)
      | _ => (0 : ℝ)
    use (by 
      intro i
      fin_cases i <;> simp [Set.mem_Icc]
      <;> all_goals norm_num 
    )
    use (by 
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals norm_num 
    )
    use 0 
    all_goals simp 
  · -- Show 40 is the least
    intro y hy 
    rcases hy with ⟨a, ha, hsum, ⟨j, heq⟩⟩ 
    have h1 : ∀ i, a i ≥ 0 := by 
      intro i 
      have h2 : a i ∈ Set.Icc (0 : ℝ) (100 : ℝ) := ha i 
      simp at h2 ⊢ 
      linarith 
    have h2 : ∀ i, a i ≤ 100 := by 
      intro i
      have h3 : a i ∈ Set.Icc (0 : ℝ) (100 : ℝ) := ha i 
      simp at h3 ⊢ 
      linarith 
    have h5 : a 0 + a 1 + a 2 + a 3 + a 4 = 440 := by 
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum ⊢ 
      linarith 
    have h3 : a j = y := by 
      tauto 
    have h6 : 40 ≤ y := by
      have eq1 : a 0 + a 1 + a 2 + a 3 + a 4 = 440 := h5 
      have eq2 : a j = y := h3
      fin_cases j <;> simp [h3] at *
      all_goals 
        norm_num [Set.mem_Icc] at ha 
        <;> 
          linarith [ha 0, ha 1, ha 2, ha 3, ha 4] 
    linarith
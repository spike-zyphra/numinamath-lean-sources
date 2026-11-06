import Mathlib



theorem algebra_610970 :
    IsGreatest {x | ∃ a : Fin 9 → ℝ, (x = a 4) ∧ (∀ i, 0 ≤ a i) ∧
      (∀ i < 8, a i ≤ a (i + 1)) ∧ ((∑ i, a i) / 9 = 10)} 18 := by
  constructor
  · -- Show 18 is in the set
    use fun i =>
      if i < 4 then (0 : ℝ) else 18
    constructor
    · -- Show that 18 = a 4.
      simp
    constructor
    · -- Show that ∀ i, 0 ≤ a i
      intro i
      fin_cases i <;> simp
      all_goals norm_num
    constructor
    · -- Show that ∀ i < 8, a i ≤ a (i + 1)
      intro i hi
      fin_cases i <;> simp at *
    · -- Show that (∑ i, a i) / 9 = 10
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      norm_num
  · -- Show that 18 is the greatest
    intro x hx
    rcases hx with ⟨a, ha4, hanonneg, hainc, ha_avg⟩
    have h1 : a 0 ≤ a 1 := hainc 0 (by simp)
    have h2 : a 1 ≤ a 2 := hainc 1 (by simp)
    have h3 : a 2 ≤ a 3 := hainc 2 (by simp)
    have h4 : a 3 ≤ a 4 := hainc 3 (by simp)
    have h5 : a 4 ≤ a 5  := hainc 4 (by simp)
    have h6 : a 5 ≤ a 6  := hainc 5 (by simp)
    have h7 : a 6 ≤ a 7  := hainc 6 (by simp)
    have h8 : a 7 ≤ a 8  := hainc 7 (by simp)
    have h3 : ∑ i : Fin 9, a i = 90 := by
      have hq : (∑ i : Fin 9, a i) / 9 = 10 := ha_avg
      have eq2 : ∑ i : Fin 9, a i = 90 := by
        linarith
      linarith
    have h3' : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 + a 6 + a 7 + a 8 = 90 := by
      simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using h3
    have ha6 : a 4 ≤ 18 := by
      linarith [h3', hanonneg 0, hanonneg 1, hanonneg 2, hanonneg 3, hanonneg 4, hanonneg 5, hanonneg 6, hanonneg 7, hanonneg 8]
    linarith [ha4, ha6]
import Mathlib

theorem algebra_4403 (a : Fin 10 → ℝ) (ha : ∑ i, a i = 300)
    (h : ∀ i, a i = (a (i - 1) + a (i + 1)) / 2) :
    IsGreatest {x | ∃ i, a i = x} 30 := by
  have h2 : ∀ i, a i = 30 := by
    intro i
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    have h6 := h 6
    have h7 := h 7
    have h8 := h 8
    have h9 := h 9
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at ha
    fin_cases i <;> simp [Finset.mem_univ, Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
    <;> norm_num [Fin.sum_univ_succ, Fin.sum_univ_zero] at ha ⊢
    <;> linarith
  constructor
  · -- Show 30 is in the image
    use 0
    rw [h2 0]
    all_goals
      norm_num
  · -- Show no value greater than 30 is in the image
    intro x hx
    rcases hx with ⟨i, hi⟩
    have hx1 : a i = 30 := h2 i
    rw [hx1] at hi
    linarith
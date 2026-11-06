import Mathlib

theorem inequalities_277346 (a : Fin 5 → ℝ) (ha : ∀ i, 30 ≤ a i) (h : ∑ i, a i = 180) :
    ∀ i, a i ≤ 60 := by 
  intro i 
  have h1 : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := by 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    linarith
  have h3 : ∀ i : Fin 5, a i ≤ 60 := by 
    intro i 
    fin_cases i 
    · -- i = 0 
      have h1' : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := h1 
      have ha1 : 30 ≤ a 1 := ha 1 
      have ha2 : 30 ≤ a 2 := ha 2 
      have ha3 : 30 ≤ a 3 := ha 3 
      have ha4 : 30 ≤ a 4 := ha 4 
      simp at *
      linarith 
    · -- i = 1 
      have h1' : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := h1 
      have ha0 : 30 ≤ a 0 := ha 0 
      have ha2 : 30 ≤ a 2 := ha 2 
      have ha3 : 30 ≤ a 3 := ha 3 
      have ha4 : 30 ≤ a 4 := ha 4 
      simp at *
      linarith 
    · -- i = 2 
      have h1' : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := h1 
      have ha0 : 30 ≤ a 0 := ha 0 
      have ha1 : 30 ≤ a 1 := ha 1 
      have ha3 : 30 ≤ a 3 := ha 3 
      have ha4 : 30 ≤ a 4 := ha 4 
      simp at *
      linarith 
    · -- i = 3 
      have h1' : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := h1 
      have ha0 : 30 ≤ a 0 := ha 0 
      have ha1 : 30 ≤ a 1 := ha 1 
      have ha2 : 30 ≤ a 2 := ha 2 
      have ha4 : 30 ≤ a 4 := ha 4 
      simp at *
      linarith 
    · -- i = 4 
      have h1' : a 0 + a 1 + a 2 + a 3 + a 4 = 180 := h1 
      have ha0 : 30 ≤ a 0 := ha 0 
      have ha1 : 30 ≤ a 1 := ha 1 
      have ha2 : 30 ≤ a 2 := ha 2 
      have ha3 : 30 ≤ a 3 := ha 3 
      simp at *
      linarith 
  exact h3 i
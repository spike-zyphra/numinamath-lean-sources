import Mathlib

theorem inequalities_191591  : IsLeast {x | ∀ a : Fin 10 → ℝ, (∑ i, a i = 100)
    ∧ (∀ i, a i + a (i + 1) + a (i + 2) ≥ 29) → (∀ i, a i ≤ x)} 13 := by 
  constructor
  · -- We need to show that 13 is in the set
    intro a ⟨h1, h2⟩ i
    have h3 := h2 0
    have h4 := h2 1
    have h5 := h2 2
    have h6 := h2 3
    have h7 := h2 4
    have h8 := h2 5
    have h9 := h2 6
    have h10 := h2 7
    have h11 := h2 8
    have h12 := h2 9
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h1 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    have h13 : a 0 ≤ 13 := by
      linarith
    have h14 : a 1 ≤ 13 := by
      linarith
    have h15 : a 2 ≤ 13 := by
      linarith
    have h16 : a 3 ≤ 13 := by
      linarith
    have h17 : a 4 ≤ 13 := by
      linarith
    have h18 : a 5 ≤ 13 := by
      linarith
    have h19 : a 6 ≤ 13 := by
      linarith
    have h20 : a 7 ≤ 13 := by
      linarith
    have h21 : a 8 ≤ 13 := by
      linarith
    have h22 : a 9 ≤ 13 := by
      linarith
    have h23 : a i ≤ 13 := by
      fin_cases i <;> simp [h13, h14, h15, h16, h17, h18, h19, h20, h21, h22]
    linarith
  · -- Let x be in the set, need to show 13 ≤ x
    intro x hx
    have h : ∀ a : Fin 10 → ℝ, (∑ i, a i = 100) ∧ (∀ i, a i + a (i + 1) + a (i + 2) ≥ 29) → (∀ i, a i ≤ x) := hx
    let a : Fin 10 → ℝ := fun i =>
      match i with
      | 0 => 13
      | 1 => 8
      | 2 => 8
      | 3 => 13
      | 4 => 8
      | 5 => 8
      | 6 => 13
      | 7 => 8
      | 8 => 8
      | 9 => 13
    have ha1 : ∑ i, a i = 100 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, a]
      norm_num
    have ha2 : ∀ i, a i + a (i + 1) + a (i + 2) ≥ 29 := by
      intro i
      fin_cases i <;> simp [a, Fin] <;> norm_num
    have ha3 := h a ⟨ha1, ha2⟩
    have ha4 : a 0 ≤ x := ha3 0
    simp [a] at ha4
    linarith
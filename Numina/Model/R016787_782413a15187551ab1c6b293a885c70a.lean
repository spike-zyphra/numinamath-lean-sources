import Mathlib

theorem algebra_118159 (a : ℝ) (A B : Set ℝ)
    (hA : A = {x | x > a}) (hB : B = {-1, 0, 1}) :
    A ∩ B = {0, 1} ↔ a ∈ Set.Ico (-1) 0 := by 
  have hA' : A = {x | x > a} := hA
  have hB' : B = {-1, 0, 1} := hB
  constructor
  · -- Assume A ∩ B = {0, 1}, prove a ∈ Set.Ico (-1) 0
    intro h_eq
    have h1 : 0 ∈ A ∩ B := by 
      rw [h_eq]
      simp
    have h2 : (1 : ℝ) ∈ A ∩ B := by
      rw [h_eq]
      simp
    have h3 : (-1 : ℝ) ∉ A ∩ B := by 
      rw [h_eq]
      norm_num 
    have h4 : (0 : ℝ) ∈ A := by 
      have h11 : 0 ∈ A ∩ B := h1
      simp [hA', hB'] at h11 ⊢
      all_goals tauto
    have h5 : (1 : ℝ) ∈ A := by 
      have h22 : (1 : ℝ) ∈ A ∩ B := h2
      simp [hA', hB'] at h22 ⊢
      all_goals tauto
    have h6 : (-1 : ℝ) ∉ A := by
      have h33 : (-1 : ℝ) ∉ A ∩ B := h3
      simp [hA', hB'] at h33 ⊢
      all_goals tauto 
    simp [hA'] at h4 h5 h6 
    have ha1 : a < 0 := by 
      nlinarith
    have ha2 : a ≥ -1 := by 
      nlinarith
    simp [Set.mem_Ico] at *
    exact ⟨by linarith, by linarith⟩
  · -- Assume a ∈ Set.Ico (-1) 0, prove A ∩ B = {0, 1}
    intro h
    simp only [Set.mem_Ico] at h
    rcases h with ⟨ha1, ha2⟩
    ext x 
    simp [hA', hB']
    constructor
    · -- Assume x ∈ A ∩ B, prove x ∈ {0, 1}
      intro h
      rcases h with ⟨h1, h2⟩ 
      rcases h2 with (rfl | rfl | rfl)
      · -- x = -1
        exfalso
        nlinarith 
      · -- x = 0 
        norm_num
      · -- x = 1 
        norm_num
    · -- Assume x ∈ {0, 1}, prove x ∈ A ∩ B
      intro h
      rcases h with (rfl | rfl)
      · -- x = 0
        constructor
        · -- Show 0 ∈ A 
          simp [show a < (0 : ℝ) by nlinarith]
        · -- Show 0 ∈ B 
          norm_num
      · -- x = 1
        constructor
        · -- Show 1 ∈ A 
          simp [show a < (1 : ℝ) by nlinarith]
        · -- Show 1 ∈ B 
          norm_num
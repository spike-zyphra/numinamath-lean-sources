import Mathlib

open Real

theorem other_60178 (f : ℝ → ℝ) :
    (∀ x, x ≠ 0 ∧ x ≠ 1 → f x + f (1 / (1 - x)) = 2 * (1 - 2 * x) / (x * (1 - x))) ↔
    ∀ x, x ≠ 0 ∧ x ≠ 1 → f x = (x + 1) / (x - 1) := by
  constructor
  · -- Assume functional equation, prove f(x) = (x + 1)/(x - 1)
    intro h_eq
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    have hx3 : 1 - x ≠ 0 := by
      intro h'
      apply hx2
      linarith 
    have eq1 := h_eq x ⟨hx1, hx2⟩
    have eq2 := h_eq (1 / (1 - x)) ⟨by 
      have hx3' : 1 - x ≠ 0 := hx3 
      field_simp [hx3']
    , by 
      by_contra h_eq1 
      have hx3' : 1 - x ≠ 0 := hx3 
      have h_eq2 : 1 = (1 - x) := by 
        field_simp [hx3'] at h_eq1 ⊢ 
        all_goals linarith 
      have h0 : x = 0 := by linarith 
      tauto
    ⟩
    have eq2' : 1 / (1 - (1 / (1 - x))) = (x - 1) / x := by 
      have hne1 : 1 - x ≠ 0 := hx3 
      have hne2 : x ≠ 0 := hx1 
      field_simp [hne1, hne2]
      <;> ring
    simp only [eq2'] at eq2
    have eq3 := h_eq ((x - 1) / x) ⟨by
      have hne1 : x ≠ 0 := hx1 
      have hne4 : x - 1 ≠ 0 := by 
        intro h'
        apply hx2 
        linarith 
      field_simp [hne1, hne4]
    , by 
      by_contra h_eq1 
      have hne1 : x ≠ 0 := hx1 
      have hne4 : x - 1 ≠ 0 := by 
        intro h'
        apply hx2 
        linarith 
      field_simp [hne1, hne4] at h_eq1 ⊢ 
      all_goals linarith 
    ⟩
    have eq3' : 1 / (1 - ((x - 1) / x)) = x := by 
      have hne1 : x ≠ 0 := hx1
      field_simp [hne1] 
      <;> ring 
    simp only [eq3'] at eq3
    have eq4 : f x = (x + 1) / (x - 1) := by 
      field_simp [(show x - 1 ≠ 0 by intro h' ; apply hx2; linarith), 
          (show x ≠ 0 by exact hx1), 
          (show (1 - x) ≠ 0 by intro h' ; apply hx2; linarith) 
        ] at eq1 eq2 eq3 ⊢ 
      ring_nf at eq1 eq2 eq3 ⊢ 
      nlinarith [sq_pos_of_ne_zero (show x - 1 ≠ 0 by intro h' ; apply hx2; linarith), sq_pos_of_ne_zero (show x ≠ 0 by exact hx1), sq_pos_of_ne_zero (show 1 - x ≠ 0 by intro h' ; apply hx2; linarith) ]
    exact eq4
  · -- Assume f(x) = (x + 1)/(x - 1), prove functional equation
    intro h_eq x ⟨hx1, hx2⟩
    have hx3 : 1 - x ≠ 0 := by 
      intro h'
      apply hx2 
      linarith 
    have eq1 : f x = (x + 1) / (x - 1) := by 
      apply h_eq x ⟨hx1, hx2⟩ 
    have eq5 : f (1 / (1 - x)) = ( (1 / (1 - x)) + 1 ) / ( (1 / (1 - x)) - 1 ) := by
      have hx5 : (1 / (1 - x)) ≠ 0 := by 
        have hx3' : 1 - x ≠ 0 := hx3 
        field_simp [hx3']
      have hx6 : (1 / (1 - x)) ≠ 1 := by 
        by_contra h_eq1 
        have hx3' : 1 - x ≠ 0 := hx3 
        have h_eq2 : 1 = (1 - x) := by 
          field_simp [hx3'] at h_eq1 ⊢ 
          all_goals linarith 
        have h0 : x = 0 := by linarith 
        tauto 
      have hx7 := h_eq (1 / (1 - x)) ⟨hx5, hx6⟩ 
      simpa using hx7 
    rw [eq1, eq5] 
    field_simp [(show 1 - x ≠ 0 by intro h' ; apply hx2; linarith), 
        (show x ≠ 0 by exact hx1), 
        (show x - 1 ≠ 0 by intro h'; apply hx2; linarith) 
      ]
    <;> ring_nf
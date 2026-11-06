import Mathlib

theorem algebra_210283 {A B C : ℤ} (h₀ : A^2 - B^2 - C^2 = 1) (h₁ : B + C - A = 3) :
    (A = 9 ∧ B = 8 ∧ C = 4) ∨ (A = 9 ∧ B = 4 ∧ C = 8) ∨ (A = -3 ∧ B = 2 ∧ C = -2) ∨
    (A = -3 ∧ B = -2 ∧ C = 2) := by 
  have h2 : A = B + C - 3 := by
    linarith
  rw [h2] at h₀
  have h3 : (B - 3) * (C - 3) = 5 := by
    nlinarith 
  have h4 : B - 3 ∣ 5 := by 
    use C - 3
    all_goals nlinarith
  have h5 : B - 3 = 1 ∨ B - 3 = 5 ∨ B - 3 = -1 ∨ B - 3 = -5 := by
    have h6 : B - 3 ∣ 5 := h4
    have h7 : B - 3 ≤ 5 := by
      apply Int.le_of_dvd (by norm_num) h6
    have h8 : B - 3 ≥ -5 := by
      have h9 : (- (B - 3)) ∣ 5 := by
        exact Int.neg_dvd.2 h6
      have h10 : - (B - 3) ≤ 5 := by
        apply Int.le_of_dvd (by norm_num) h9
      omega
    interval_cases (B - 3) <;> tauto
  rcases h5 with (h51 | h52 | h53 | h54)
  · -- Assume B - 3 = 1 so b = 4, and c - 3 = 5 so c = 8
    have B_eq4 : B = 4 := by 
      linarith [h51]
    have C_eq8 : C = 8 := by
      have h6 : (C - 3) = 5 := by
        rw [show B - 3 = 1 by linarith [h51]] at h3
        linarith
      linarith
    have A_eq9 : A = 9 := by
      rw [show B = 4 by linarith, show C = 8 by linarith] at h2
      linarith
    simp [A_eq9, B_eq4, C_eq8]
  · -- Assume B - 3 = 5 so b = 8, c - 3 = 1 so c = 4
    have B_eq8 : B = 8 := by 
      linarith [h52]
    have C_eq4 : C = 4 := by
      have h6 : (C - 3) = 1 := by
        rw [show B - 3 = 5 by linarith [h52]] at h3
        linarith
      linarith
    have A_eq9 : A = 9 := by
      rw [show B = 8 by linarith, show C = 4 by linarith] at h2
      linarith
    simp [A_eq9, B_eq8, C_eq4]
  · -- Assume b - 3 = -1 so b = 2, c - 3 = -5 so c = -2
    have B_eq2 : B = 2 := by 
      linarith [h53]
    have C_eq2 : C = -2 := by
      have h7 : (C - 3) = -5 := by
        rw [show B - 3 = -1 by linarith [h53]] at h3
        linarith
      linarith
    have A_eq3 : A = -3 := by
      rw [show B = 2 by linarith, show C = -2 by linarith] at h2
      linarith
    simp [A_eq3, B_eq2, C_eq2]
  · -- Assume b - 3 = -5 so b = -2, c - 3 = -1 so c = 2
    have B_eq2 : B = -2 := by 
      linarith [h54]
    have C_eq2 : C = 2 := by
      have h8 : (C - 3) = -1 := by
        rw [show B - 3 = -5 by linarith [h54]] at h3
        linarith
      linarith
    have A_eq3 : A = -3 := by
      rw [show B = -2 by linarith, show C = 2 by linarith] at h2
      linarith
    simp [A_eq3, B_eq2, C_eq2]
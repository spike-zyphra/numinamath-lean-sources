import Mathlib


noncomputable abbrev algebra_97717_solution : ℕ := 67

theorem algebra_97717 {x y : ℝ} (P : ℝ × ℝ) (hP : 8 * P.2 = 15 * P.1) (Q : ℝ × ℝ) (hQ : 10 * Q.2 = 3 * Q.1) (R : ℝ × ℝ) (hR : R.1 = 8 ∧ R.2 = 6) (n m : ℕ) (hmn : m > 0 ∧ n > 0 ∧ m.Coprime n ∧ n*Real.sqrt ((P.1 - Q.1)^2 + (P.2 - Q.2)^2) = m) (hmid : (P.1+Q.1)/2=R.1 ∧ (P.2+Q.2)/2=R.2) :  m+n = algebra_97717_solution := by
  rcases hmn with ⟨h1, h2, h3, h4⟩
  rcases hR with ⟨h5, h6⟩
  rcases hmid with ⟨h7, h8⟩
  have eq1 : P.1 + Q.1 = 16 := by
    have eq1' : (P.1 + Q.1) / 2 = R.1 := h7
    rw [h5] at eq1'
    linarith
  have eq2 : P.2 + Q.2 = 12 := by
    have eq2' : (P.2 + Q.2) / 2 = R.2 := h8
    rw [h6] at eq2'
    linarith
  have eq3 : P.1 = 32 / 7 := by 
    nlinarith [eq1, eq2, hP, hQ]
  have eq4 : Q.1 = 80 / 7 := by 
    nlinarith [eq1, eq2, hP, hQ]
  have eq5 : P.2 = 60 / 7 := by
    rw [eq3] at hP
    linarith
  have eq6 : Q.2 = 24 / 7 := by
    rw [eq4] at hQ
    linarith
  have eq7 : (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2 = (3600 / 49 : ℝ) := by
    rw [eq3, eq4, eq5, eq6]
    norm_num
  have eq8 : Real.sqrt ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) = (60 / 7 : ℝ) := by
    rw [eq7]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h7 : (↑n : ℝ) * (60 / 7 : ℝ) = (↑m : ℝ) := by
    have h8 : (↑n : ℝ) * Real.sqrt ((P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2) = (↑m : ℝ) := by
      exact_mod_cast h4
    rw [eq8] at h8
    linarith [h8]
  have eq9 : 7 * m = 60 * n := by
    have h8 : (7 : ℝ) * (↑m : ℝ) = (60 : ℝ) * (↑n : ℝ) := by
      nlinarith [h7]
    have h9 : 7 * m = 60 * n := by
      exact_mod_cast h8
    linarith [h9]
  have eq10 : m = 60 := by
    have h12 : m ∣ 60 * n := by 
      use 7 
      linarith [eq9] 
    have h13 : m ∣ 60 := by 
      have h14 : m ∣ 60 * n := h12 
      have h15 : m.Coprime n := h3 
      have h16 : m ∣ 60 := by 
        exact Nat.Coprime.dvd_of_dvd_mul_right h15 h14 
      exact_mod_cast h16 
    have h14 : m ≤ 60 := by 
      exact Nat.le_of_dvd (by omega) h13 
    interval_cases m <;> omega 
    all_goals omega 
    all_goals nlinarith [eq9] 
  have eq11 : n = 7 := by 
    have h18 : 7 * m = 60 * n := eq9 
    rw [eq10] at h18 
    omega 
  simp [eq10, eq11, algebra_97717_solution] 
  all_goals linarith 
  all_goals norm_num 
  all_goals linarith
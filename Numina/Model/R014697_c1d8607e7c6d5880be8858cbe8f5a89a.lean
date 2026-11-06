import Mathlib

theorem algebra_305395 {a : ℤ} (h : ∃ m n : ℤ, m ≠ n ∧ m^2 + (a - 6)*m + a = 0 ∧ n^2 + (a - 6)*n + a = 0) :
    a = 0 ∨ a = 16 := by 
  rcases h with ⟨m, n, h1, h2, h3⟩
  have h4 : m^2 + (a - 6) * m + a = 0 := h2
  have h5 : n^2 + (a - 6) * n + a = 0 := h3
  have h6 : (m - n) * (m + n + (a - 6)) = 0 := by 
    nlinarith 
  have h7 : m + n + (a - 6) = 0 := by 
    apply_fun (fun x => x / (m - n)) at h6
    field_simp [show m - n ≠ 0 by 
      intro h8
      apply h1 
      linarith 
    ] at h6 
    <;> nlinarith 
  have h8 : m + n = 6 - a := by 
    linarith 
  have h9 : m * n = a := by 
    nlinarith [sq_pos_of_ne_zero (show (m - n : ℤ) ≠ 0 by 
      intro h8
      apply h1
      linarith 
    ), sq_nonneg (m - n), sq_nonneg (m + n - (6 - a)), h8, h2, h3]
  have h10 : (m + 1) * (n + 1) = 7 := by 
    nlinarith [h8, h9]
  have h11 : (m + 1) * (n + 1) = 7 := h10 
  have h12 : m + 1 ∣ 7 := by 
    use n + 1 
    all_goals linarith [h11]
  have h13 : m + 1 ∣ 7 := h12 
  have h14 : m + 1 = 1 ∨ m + 1 = 7 ∨ m + 1 = -1 ∨ m + 1 = -7 := by 
    have h15 : m + 1 ∣ 7 := h13 
    have h16 : m + 1 ∣ 7 := h15 
    have h17 : m + 1 ≤ 7 := by 
      apply Int.le_of_dvd (by norm_num) h16 
    have h18 : m + 1 ≥ -7 := by 
      have h19 : -(m + 1) ∣ 7 := by 
        exact Int.neg_dvd.2 h16 
      have h20 : -(m + 1) ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h19 
      linarith 
    interval_cases (m + 1) <;> tauto 
  rcases h14 with (h15 | h16 | h17 | h18)
  · -- case (m + 1) = 1 
    have h18 : n + 1 = 7 := by 
      nlinarith [h11, h15] 
    have h19 : m = 0 := by 
      linarith 
    have h20 : n = 6 := by 
      linarith 
    have h21 : a = 0 := by 
      nlinarith [h19, h20, h9] 
    left 
    exact h21 
  · -- case (m + 1) = 7 
    have h19 : n + 1 = 1 := by 
      nlinarith [h11, h16] 
    have h20 : m = 6 := by 
      linarith 
    have h21 : n = 0 := by 
      linarith 
    have h22 : a = 0 := by 
      nlinarith [h20, h21, h9] 
    left 
    exact h22 
  · -- case (m + 1) = -1 
    have h20 : n + 1 = -7 := by 
      nlinarith [h11, h17] 
    have h21 : m = -2 := by 
      linarith 
    have h22 : n = -8 := by 
      linarith 
    have h23 : a = 16 := by 
      nlinarith [h21, h22, h9] 
    right 
    exact h23 
  · -- case (m + 1) = -7 
    have h21 : n + 1 = -1 := by 
      nlinarith [h11, h18] 
    have h22 : m = -8 := by 
      linarith 
    have h23 : n = -2 := by 
      linarith 
    have h24 : a = 16 := by 
      nlinarith [h22, h23, h9] 
    right 
    exact h24
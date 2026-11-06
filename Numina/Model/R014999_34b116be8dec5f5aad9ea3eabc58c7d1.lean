import Mathlib

theorem algebra_80616 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h1: 5 / a = b + c) (h2: 10 / b = c + a)(h3: 13 / c = a + b) (m n : ℕ) (mpos : 0 < m) (npos : 0 < n) (mncop : m.Coprime n) (hmn : a + b + c = m / n) : m + n = 55 := by 
  have eq1 : a * (b + c) = 5 := by
    have h1' : 0 < a := by linarith
    field_simp at h1 ⊢
    nlinarith 
  have eq2 : b * (c + a) = 10 := by 
    have h2' : 0 < b := by linarith
    field_simp at h2 ⊢ 
    nlinarith 
  have eq3 : c * (a + b) = 13 := by 
    have h3' : 0 < c := by linarith 
    field_simp at h3 ⊢ 
    nlinarith 
  have eq4 : a * b = 1 := by 
    nlinarith 
  have eq5 : a * c = 4 := by 
    nlinarith 
  have eq6 : b * c = 9 := by 
    nlinarith 
  have eq7 : a ^ 2 = 4 / 9 := by 
    nlinarith 
  have eq8 : a = 2 / 3 := by 
    nlinarith [sq_pos_of_pos ha] 
  have eq9 : b = 3 / 2 := by 
    nlinarith [eq4, eq8] 
  have eq10 : c = 6 := by 
    nlinarith 
  have hmn_eq : (m : ℝ) / (n : ℝ) = (49 / 6 : ℝ) := by 
    have h1 : a + b + c = (m : ℝ) / (n : ℝ) := by linarith [hmn]
    have h2 : a + b + c = (49 / 6 : ℝ) := by 
      nlinarith 
    linarith 
  have h2_eq : m * 6 = 49 * n := by 
    have hmn_eq2 : (m : ℝ) / (n : ℝ) = (49 : ℝ) / (6 : ℝ) := by 
      linarith [hmn_eq] 
    have hnne : (n : ℝ) ≠ 0 := by 
      have h1 : (n : ℕ) > (0 : ℕ) := by linarith 
      have h1' : (n : ℝ) > (0 : ℝ) := by exact_mod_cast h1 
      linarith 
    field_simp [hnne] at hmn_eq2 ⊢ 
    have hmn_eq3 : (m : ℝ) * 6 = 49 * (n : ℝ) := by 
      linarith 
    exact_mod_cast hmn_eq3 
  -- Prove m = 49
  have h5m : m = 49 := by
    have h41 : m ∣ 49 := by 
      have h53 : m ∣ 49 * n := by 
        use 6 
        all_goals linarith [h2_eq] 
      have h56 : Nat.Coprime m n := mncop 
      have h13 : m ∣ 49 := by 
        apply Nat.Coprime.dvd_of_dvd_mul_right h56 h53 
      exact_mod_cast h13 
    have h411 : m = 1 ∨ m = 7 ∨ m = 49 := by
      have h411 : m ∣ 49 := h41 
      have h4111 : m ≤ 49 := by 
        exact Nat.le_of_dvd (by linarith) h411 
      interval_cases m <;> norm_num at h411 
      <;> tauto 
    rcases h411 with (h411 | h411 | h411)
    · -- m = 1 
      rw [show m = 1 by omega] at h2_eq 
      omega 
    · -- m = 7 
      rw [show m = 7 by omega] at h2_eq 
      omega 
    · -- m = 49 
      omega 
  -- Prove n = 6 
  have h5n : n = 6 := by 
    rw [show m = 49 by omega] at h2_eq 
    omega 
  -- Now, conclude m + n = 55 
  calc 
    m + n = 49 + 6 := by rw [h5m, h5n] 
    _ = 55 := by norm_num
import Mathlib

theorem algebra_98311 {m n : ℕ} {x : ℝ} (hx : x > 0)
(h: Real.logb (2^x) (3^20) = Real.logb (2^(x + 3)) (3^2020))
(h2: m > 0 ∧ n > 0 ∧ m.Coprime n ∧ x = m / n)
: m + n = 103 := by
  rcases h2 with ⟨hm, hn, hcop, hx_eq⟩
  have h1 : Real.logb (2^x) (3^20) = 20 * Real.log 3 / (x * Real.log 2) := by
    have h1 : Real.logb (2^x) (3^20) = Real.log (3^20) / Real.log (2^x) := by 
      field_simp [Real.logb]
    rw [h1]
    have h2 : Real.log (3^20) = 20 * Real.log 3 := by 
      simp [Real.log_pow]
    have h3 : Real.log (2^x) = x * Real.log 2 := by 
      rw [Real.log_rpow]
      all_goals linarith
    rw [h2, h3]
  have h2' : Real.logb (2^(x + 3)) (3^2020) = 2020 * Real.log 3 / ((x + 3) * Real.log 2) := by
    have h1 : Real.logb (2^(x + 3)) (3^2020) = Real.log (3^2020) / Real.log (2^(x + 3)) := by
      field_simp [Real.logb]
    rw [h1]
    have h2 : Real.log (3^2020) = 2020 * Real.log 3 := by 
      simp [Real.log_pow]
    have h3 : Real.log (2^(x + 3)) = (x + 3) * Real.log 2 := by 
      rw [Real.log_rpow]
      all_goals linarith
    rw [h2, h3]
  rw [h1, h2'] at h
  have h3 : Real.log 3 > 0 := by
    apply Real.log_pos 
    all_goals linarith 
  have h4 : Real.log 2 > 0 := by 
    apply Real.log_pos 
    all_goals linarith 
  have hx1 : x * Real.log 2 > 0 := by 
    positivity 
  have hx2 : (x + 3) * Real.log 2 > 0 := by 
    positivity 
  have h5 : 20 * Real.log 3 * ((x + 3) * Real.log 2) = 2020 * Real.log 3 * (x * Real.log 2) := by
    have hx6 : x * Real.log 2 ≠ 0 := by positivity 
    have hx7 : (x + 3) * Real.log 2 ≠ 0 := by positivity 
    have hx8 : Real.log 3 ≠ 0 := by linarith 
    field_simp [hx6, hx7, hx8] at h ⊢ 
    nlinarith [h]
  have h6 : 20 * ((x + 3) * Real.log 2) = 2020 * (x * Real.log 2) := by
    have h7 : Real.log 3 ≠ 0 := by linarith
    apply (mul_left_inj' (show Real.log 3 ≠ 0 by linarith)).mp
    linarith [h5, mul_pos h3 h4, h4, h3]
  have hx200 : x = (3 / 100 : ℝ) := by
    nlinarith [h6, Real.log_pos (show (2 : ℝ) > 1 by norm_num)]
  rw [hx_eq] at hx200
  have h10 : (m : ℝ) / (n : ℝ) = (3 / 100 : ℝ) := by 
    linarith [hx200 ]
  have h11 : m * 100 = 3 * n := by 
    have eq1 : (m : ℝ) * (100 : ℝ) = (3 * (n : ℝ) ) := by 
      have hne1 : (n : ℝ) ≠ 0 := by positivity 
      field_simp [hne1] at h10 ⊢ 
      nlinarith [ h10, hx200 ] 
    exact_mod_cast eq1 
  have h40 : m * 100 = 3 * n := h11 
  have h30 : m ∣ 3 := by 
    have h12 : m ∣ 3 * n := by 
      use 100 
      linarith 
    have h31 : Nat.gcd m n = 1 := by 
      rw [Nat.coprime_iff_gcd_eq_one] at hcop 
      exact hcop 
    have h32 : m ∣ 3 := by 
      have h7 : m ∣ 3 * n := h12 
      have h8 : Nat.gcd m n = 1 := h31 
      have h9 : m ∣ 3 := by 
        exact Nat.Coprime.dvd_of_dvd_mul_right h8 h7 
      exact h9 
    exact h32 
  have : m ≤ 3 := by 
    exact Nat.le_of_dvd (show 0 < 3 by norm_num) h30 
  interval_cases m <;> omega
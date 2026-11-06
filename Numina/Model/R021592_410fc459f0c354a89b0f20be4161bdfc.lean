import Mathlib

theorem algebra_120566 {n m : ℕ} (hcoprime : Nat.Coprime n m)
    (h : 2013 * 2013 / (2014 * 2014 + 2012 : ℚ) = n / m) :
    m + n = 1343 := by
  have h1 : (2013 * 2013 / (2014 * 2014 + 2012 : ℚ) : ℚ) = (671 : ℚ) / (672 : ℚ) := by
    norm_num
  rw [h1] at h
  have h2 : (671 : ℚ) * (m : ℚ) = (672 : ℚ) * (n : ℚ) := by
    field_simp [(show (672 : ℚ) ≠ 0 by norm_num), (show (m : ℚ) ≠ 0 by
      by_contra h'
      have : (m : ℚ) = 0 := by linarith
      rw [this] at h
      field_simp [(show (672 : ℚ) ≠ 0 by norm_num)] at h
    )] at h ⊢
    linarith
  have h3 : (671 : ℕ) * m = (672 : ℕ) * n := by
    exact_mod_cast h2
  -- Now to deduce n and m from the equation and coprime
  have h4 : n = 671 := by
    have h6 : Nat.Coprime n m := hcoprime
    have h7 : n ∣ 671 * m := by
      use 672
      linarith
    have h8 : n ∣ 671 := by
      have h9 : n ∣ 671 * m := h7
      have h10 : Nat.Coprime n m := h6
      have h11 : n ∣ 671 := by
        apply Nat.Coprime.dvd_of_dvd_mul_right h10 h9
      exact h11
    -- Now n divides 671, so n ∈ {1, 11, 61, 671}
    have h9 : n = 1 ∨ n = 11 ∨ n = 61 ∨ n = 671 := by
      have h8 : n ∣ 671 := h8
      have h9 : n ≤ 671 := by 
        exact Nat.le_of_dvd (by linarith) h8
      interval_cases n <;> norm_num at h8 <;> tauto
    rcases h9 with (h9 | h9 | h9 | h9)
    · -- n = 1
      rw [show n = 1 by linarith] at h3
      omega
    · -- n = 11
      rw [show n = 11 by linarith] at h3
      omega
    · -- n = 61
      rw [show n = 61 by linarith] at h3
      omega
    · -- n = 671
      omega
  have h5 : m = 672 := by
    rw [h4] at h3
    omega
  linarith [h4, h5]
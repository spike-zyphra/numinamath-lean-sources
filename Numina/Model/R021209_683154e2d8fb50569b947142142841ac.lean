import Mathlib

theorem algebra_275833 {m n : ℕ} (hm : m > 0) (hn : n > 0)
    (hcoprime : Nat.Coprime m n) (h : (2 + 4 + 6 + 8 : ℚ) / (1 + 3 + 5 + 7) - (1 + 3 + 5 + 7) / (2 + 4 + 6 + 8) = m / n) :
    10 * m + n = 110 := by
  have h1 : (m : ℚ) > (0 : ℚ) := by
    exact_mod_cast hm
  have h2 : (n : ℚ) > (0 : ℚ) := by
    exact_mod_cast hn
  have h3 : (2 + 4 + 6 + 8 : ℚ) / (1 + 3 + 5 + 7) - (1 + 3 + 5 + 7) / (2 + 4 + 6 + 8) = (9 / 20 : ℚ) := by 
    norm_num
  have h4 : (m : ℚ) / (n : ℚ) = (9 / 20 : ℚ) := by
    linarith [h, h3]
  have h5 : (m : ℚ) * 20 = 9 * (n : ℚ) := by
    have h5 : (m : ℚ) / (n : ℚ) = (9 : ℚ) / (20 : ℚ) := by
      linarith [h4]
    have hnne : (n : ℚ) ≠ 0 := by
      have : (n : ℚ) > 0 := h2
      linarith
    field_simp [hnne] at h5 ⊢
    linarith
  have h6 : m * 20 = 9 * n := by
    exact_mod_cast h5
  have h7 : m = 9 := by
    have h8 : m ∣ 9 * n := by
      use 20
      linarith [h6]
    have h10 : m ∣ 9 := by
      have h11 : m ∣ 9 * n := h8
      have h12 : Nat.Coprime m n := hcoprime
      have h13 : m ∣ 9 := by
        apply Nat.Coprime.dvd_of_dvd_mul_right h12 h11
      exact h13
    have h11 : m ∣ 9 := h10
    have h12 : m ≤ 9 := by
      exact Nat.le_of_dvd (show 0 < 9 by norm_num) h11
    have h13 : m = 1 ∨ m = 3 ∨ m = 9 := by
      interval_cases m <;> norm_num at h11 ⊢
    rcases h13 with h13 | h13 | h13
    · -- m = 1
      rw [show m = 1 by linarith [h13]] at h6
      omega
    · -- m = 3
      rw [show m = 3 by linarith [h13]] at h6
      omega
    · -- m = 9
      linarith [h13]
  have h15 : n = 20 := by
    linarith [h7, h6]
  linarith [h7, h15]
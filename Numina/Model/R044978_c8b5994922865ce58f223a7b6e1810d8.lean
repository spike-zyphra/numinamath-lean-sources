import Mathlib

theorem algebra_51523 (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmn : Nat.Coprime m n) (h : (1 + 3 / 4 : ℝ) * (1 - 1 / 4) * (1 + 1 / 3) * (1 - 1 / 5) * (1 + 1 / 7) * (1 - (m / n : ℝ)) = 1) :
    m + n = 11 := by
  have h1 : (m : ℝ) > (0 : ℝ) := by exact_mod_cast hm
  have h2 : (n : ℝ) > (0 : ℝ) := by exact_mod_cast hn
  have eq1 : (1 + (3 / 4 : ℝ)) * (1 - (1 / 4 : ℝ)) * (1 + (1 / 3 : ℝ)) * (1 - (1 / 5 : ℝ)) * (1 + (1 / 7 : ℝ)) * (1 - (m / n : ℝ)) = 1 := h
  have h3 : (1 + (3 / 4 : ℝ)) * (1 - (1 / 4 : ℝ)) * (1 + (1 / 3 : ℝ)) * (1 - (1 / 5 : ℝ)) * (1 + (1 / 7 : ℝ)) = (8 / 5 : ℝ) := by
    norm_num 
  have h4 : (8 / 5 : ℝ) * (1 - (m / n : ℝ)) = 1 := by
    rw [h3] at eq1 
    linarith
  have h5 : (1 - (m / n : ℝ)) = (5 / 8 : ℝ) := by 
    linarith
  have h6 : (m : ℝ) / (n : ℝ) = (3 / 8 : ℝ) := by 
    have h7 : (1 - (m / n : ℝ)) = (5 / 8 : ℝ) := h5 
    have eq2 : (m / n : ℝ) = 1 - (5 / 8 : ℝ) := by
      have eq3 : (1 - (m / n : ℝ)) = (5 / 8 : ℝ) := h5 
      linarith 
    rw [eq2]
    norm_num 
  have eq4 : (m : ℝ) * 8 = (3 : ℝ) * (n : ℝ) := by
    have h7 : (m : ℝ) / (n : ℝ) = (3 / 8 : ℝ) := h6 
    have hn' : (n : ℝ) ≠ 0 := by linarith 
    field_simp at h7 ⊢ 
    linarith 
  have h7 : m * 8 = 3 * n := by
    exact_mod_cast eq4
  -- now we have equation for natural numbers `8 * m = 3 * n` with co-prime
  have h7' : m * 8 = 3 * n := h7 
  -- Now prove that from coprime and 8 * m = 3 * n
  have h11 : m ∣ 3 * n := by 
    use 8 
    linarith 
  have h12 : m ∣ 3 := by 
    have h13 : Nat.Coprime m n := hmn 
    have h14 : m ∣ 3 * n := h11 
    have h15 : m ∣ 3 := by 
      apply h13.dvd_of_dvd_mul_right h14 
    exact h15 
  -- Now since m divides 3, and m > 0 so m = 1 or 3.
  have h13 : m = 1 ∨ m = 3 := by 
    have h14 : m ∣ 3 := h12 
    have h15 : m ≤ 3 := by 
      exact Nat.le_of_dvd (by norm_num) h14 
    interval_cases m <;> try tauto 
  rcases h13 with (h14 | h15)
  · -- Assume m = 1 
    have h16 : m = 1 := h14 
    have h17 : 1 * 8 = 3 * n := by 
      rw [h16] at h7' 
      omega 
    omega 
  · -- Assume m = 3 
    have h18 : m = 3 := h15 
    -- get n
    have h19 : 3 * 8 = 3 * n := by 
      rw [h18] at h7' 
      omega 
    have h20 : n = 8 := by 
      omega 
    linarith
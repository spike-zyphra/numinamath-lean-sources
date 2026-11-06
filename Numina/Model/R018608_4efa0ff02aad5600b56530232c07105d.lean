import Mathlib

theorem algebra_267167 (k : ℤ) (h : ∃ x : ℕ, x > 0 ∧ k * x - 5 = 2021 * x + 2 * k) :
    k ≤ 6068 := by 
  rcases h with ⟨x, hx_pos, heq⟩
  have hx1 : x ≥ 1 := by
    omega 
  have eq1 : k * (x : ℤ) - 5 = 2021 * (x : ℤ) + 2 * k := by
    exact_mod_cast heq
  have hx2 : (k - 2021 : ℤ) * (x : ℤ) = 2 * k + 5 := by 
    nlinarith 
  have hx3 : (x : ℤ) > 0 := by
    exact_mod_cast hx_pos 
  have h1 : (k - 2021 : ℤ) ∣ 2 * k + 5 := by 
    use (x : ℤ)
    all_goals linarith 
  have h2 : (k - 2021 : ℤ) ∣ 4047 := by 
    have h3 : (k - 2021 : ℤ) ∣ 2 * k + 5 := h1 
    have h4 : (k - 2021 : ℤ) ∣ 2 * (k - 2021) := by 
      apply dvd_mul_of_dvd_right 
      exact dvd_refl (k - 2021) 
    have h5 : (k - 2021 : ℤ) ∣ (2 * k + 5 - 2 * (k - 2021)) := by 
      apply Dvd.dvd.sub 
      · exact h3 
      · exact h4 
    have h6 : (2 * k + 5 - 2 * (k - 2021) : ℤ) = 4047 := by 
      nlinarith 
    rw [h6] at h5 
    exact h5 
  by_cases h5 : (k - 2021 : ℤ) ≤ 0 
  · 
    have hk2 : (k - 2021 : ℤ) ≤ 0 := by linarith 
    have eq0 : (k - 2021 : ℤ) * (x : ℤ) = 2 * k + 5 := hx2 
    have h6 : (k - 2021 : ℤ) * (x : ℤ) ≤ 0 := by 
      have hk2 : (k - 2021 : ℤ) ≤ 0 := by linarith 
      have hx3 : (x : ℤ) > 0 := by 
        exact_mod_cast hx_pos 
      nlinarith 
    have h7 : 2 * k + 5 ≤ 0 := by 
      linarith [eq0, h6] 
    omega 
  · 
    have h6 : (k - 2021 : ℤ) > 0 := by 
      omega 
    have h7 : (k - 2021 : ℤ) ≤ 4047 := by 
      apply Int.le_of_dvd (by norm_num) h2 
    omega
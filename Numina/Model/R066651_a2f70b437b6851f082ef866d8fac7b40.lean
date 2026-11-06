import Mathlib

theorem algebra_297293 (k : ℤ) (h : ∃ n : ℕ, 0 < n ∧ 9 * n - 17 = k * n) :
    k = 8 ∨ k = -8 := by 
  rcases h with ⟨n, hn_pos, h_eq⟩
  have h_eq_z : (9 : ℤ) * (n : ℤ) - 17 = k * (n : ℤ) := by 
    norm_num at h_eq ⊢
    all_goals exact_mod_cast h_eq
  have eq1 : (n : ℤ) * (9 - k) = 17 := by 
    linarith [h_eq_z]
  have h1 : (n : ℤ) ∣ 17 := by 
    use (9 - k)
    all_goals linarith
  have h2 : (n : ℤ) ≥ 1 := by 
    exact_mod_cast show (n ≥ 1) by linarith
  have h3 : (n : ℤ) ≤ 17 := by 
    exact Int.le_of_dvd (by norm_num) h1
  have h4 : (n : ℤ) = 1 ∨ (n : ℤ) = 17 := by
    have h5 : (n : ℤ) ∣ 17 := h1
    have h5' : (n : ℤ) ≤ 17 := h3
    have h6 : (n : ℤ) ≥ 1 := h2
    have h7 : (n : ℤ) = 1 ∨ (n : ℤ) = 17 := by 
      have h8 : (n : ℤ) ≤ 17 := h3
      interval_cases (n : ℤ) <;> norm_num at *
      <;> try { tauto }
      <;> try { 
        norm_num at h5 
        <;> try { tauto }
      }
    exact h7
  rcases h4 with hn | hn
  · 
    rw [hn] at eq1
    have h8 : (9 - k : ℤ) = 17 := by 
      nlinarith
    have hk : k = -8 := by 
      linarith 
    right 
    exact hk 
  · 
    rw [hn] at eq1 
    have h8 : (9 - k : ℤ) = 1 := by 
      nlinarith 
    have hk : k = 8 := by 
      linarith 
    left 
    exact hk
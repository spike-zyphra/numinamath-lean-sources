import Mathlib

theorem number_theory_16354 (y : ℝ) (hy : y = 0.42 + 0.01 * ∑' n : ℕ, 0.153 * 0.001 ^ n)
    (x : ℕ) (hx : x / 99900 = y) : x = 42111 := by
  have eq_y : y = (42111 : ℝ) / 99900 := by
    rw [hy]
    have h1 : ∑' n : ℕ, (0.153 : ℝ) * (0.001 : ℝ) ^ n = (0.153 / (1 - 0.001) : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one]
      all_goals norm_num
    rw [h1]
    norm_num
  have h_eq : (x : ℝ) / 99900 = (42111 : ℝ) / 99900 := by 
    linarith [hx, eq_y]
  have h_eq2 : (x : ℝ) = 42111 := by 
    have h1 : (x : ℝ) / 99900 = (42111 : ℝ) / 99900 := h_eq
    field_simp at h1 ⊢
    linarith
  have h_eq3 : x = 42111 := by 
    exact_mod_cast h_eq2
  exact h_eq3
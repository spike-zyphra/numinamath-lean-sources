import Mathlib

theorem algebra_179088 (v : ℝ) (h : v > 0) (h1 : ∃ x y : ℕ, x < 10 ∧ y < 10 ∧
    x * 10 + y = v * 12.42 ∧ y * 10 + x = v * 13.05 ∧ x * 100 + 0 * 10 + y = v * 14.10) :
    v = 90 := by
  rcases h1 with ⟨x, y, hx, hy, h12, h2, h3⟩
  have h12' : (x * 10 + y : ℝ) = v * 12.42 := by
    norm_num at h12 ⊢
    exact_mod_cast h12
  have h2' : (y * 10 + x : ℝ) = v * 13.05 := by
    norm_num at h2 ⊢
    exact_mod_cast h2
  have h3' : ((x * 100 + 0 * 10 + y) : ℝ) = v * 14.10 := by
    norm_num at h3 ⊢
    exact_mod_cast h3
  have h4 : (x : ℝ) < 10 := by exact_mod_cast (show (x : ℕ) < 10 by linarith)
  have h5 : (y : ℝ) < 10 := by exact_mod_cast (show (y : ℕ) < 10 by linarith)
  have h6 : (x : ℝ) ≥ 0 := by exact_mod_cast (show (x : ℕ) ≥ 0 by omega)
  have h7 : (y : ℝ) ≥ 0 := by exact_mod_cast (show (y : ℕ) ≥ 0 by omega)
  have v_eq : v = 90 := by
    norm_num at h12' h2' h3'
    have h8 : (x : ℝ) ≤ 9 := by linarith
    have h9 : (y : ℝ) ≤ 9 := by linarith
    nlinarith [sq_nonneg ((x : ℝ) - 1), sq_nonneg ((y : ℝ) - 8), sq_nonneg (v - 90)]
  exact v_eq
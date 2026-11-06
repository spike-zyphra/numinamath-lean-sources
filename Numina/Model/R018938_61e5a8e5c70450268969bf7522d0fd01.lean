import Mathlib

theorem number_theory_5939 (a b : ℤ) (ha : 0 < a) (hb : 0 < b)
    (h : ∃ k : ℤ, 0 < k ∧ (1 / a - 1 / b : ℝ) = k) : a = b := by
  rcases h with ⟨k, hk_pos, h_eq⟩
  have h_eq1 : (b - a : ℝ) = (k : ℝ) * (a * b : ℝ) := by
    field_simp at h_eq ⊢
    nlinarith
  have h_eq2 : (b - a : ℤ) = k * (a * b) := by
    exact_mod_cast h_eq1
  nlinarith [mul_pos ha hb, mul_pos ha (show 0 < k by linarith), 
          mul_pos (show 0 < k by linarith) hb
        ]
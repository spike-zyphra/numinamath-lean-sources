import Mathlib

theorem algebra_184813 {r b : ℕ} (h₀ : r * 3 = b * 7) (h₁ : r > 0) (h₂ : b > 0)
    (x : ℝ) (hx : x > 0) (h₃ : (r + x) * 5 = b * 14) :
    x / r * 100 = 20 := by 
  have h0' : (r : ℝ) * 3 = (b : ℝ) * 7 := by
    exact_mod_cast h₀
  have h3' : (r + x) * 5 = (b : ℝ) * 14 := by
    exact_mod_cast h₃
  have hr : (r : ℝ) > 0 := by
    exact_mod_cast show (r : ℕ) > 0 by linarith
  have h4 : (x : ℝ) = (r : ℝ) / 5 := by
    have hb : (b : ℝ) = (3 / 7) * (r : ℝ) := by
      linarith [h0']
    rw [hb] at h3'
    nlinarith 
  have : (x : ℝ) / (r : ℝ) * 100 = 20 := by 
    have hr' : (r : ℝ) ≠ 0 := by 
      linarith [show (r : ℝ) > 0 from by exact_mod_cast show (r : ℕ) > 0 by linarith]
    have h5 : (x : ℝ) = (r : ℝ) / 5 := h4
    rw [h5]
    field_simp
    <;> nlinarith
  exact_mod_cast this
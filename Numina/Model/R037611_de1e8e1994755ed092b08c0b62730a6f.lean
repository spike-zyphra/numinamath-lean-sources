import Mathlib

theorem algebra_168211 {x : ℕ} {t : ℝ} (hx : x > 75)
   (h1 : t / (x - 75) - t / x = 20) (h2 : t / x - t / (x + 100) = 15) :
    x = 300 := by

  have h3 : x ≥ 76 := by
    omega

  have hx1 : (x : ℝ) > 75 := by
    have h1' : (x : ℝ) ≥ (76 : ℝ) := by
      exact_mod_cast h3
    linarith

  have hx2 : (x : ℝ) - 75 ≠ 0 := by
    linarith

  have hx3 : (x : ℝ) ≠ 0 := by
    nlinarith

  have hx4 : (x + 100 : ℝ) ≠ 0 := by
    nlinarith

  have eq1 : 75 * (t : ℝ) = 20 * ((x : ℝ) - 75) * (x : ℝ) := by
    field_simp [(show (x : ℝ) - 75 ≠ 0 by assumption), (show (x : ℝ) ≠ 0 by assumption)] at h1 ⊢
    ring_nf at h1 ⊢
    nlinarith [h1]

  have eq2 : 100 * (t : ℝ) = 15 * (x : ℝ) * (x + 100 : ℝ) := by
    field_simp [(show (x : ℝ) ≠ 0 by assumption), (show (x + 100 : ℝ) ≠ 0 by assumption)] at h2 ⊢
    ring_nf at h2 ⊢
    nlinarith [h2]

  have eq3 : (x : ℝ) = (300 : ℝ) := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < (4 : ℝ) by norm_num), sq_pos_of_pos (show (0 : ℝ) < (5 : ℝ) by norm_num)]

  have eq4 : x = 300 := by
    have h1 : (x : ℝ) = (300 : ℝ) := eq3
    exact_mod_cast h1

  exact eq4
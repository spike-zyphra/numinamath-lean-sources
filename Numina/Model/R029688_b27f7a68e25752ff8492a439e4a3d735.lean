import Mathlib

theorem algebra_248888 (d vi vf ve: ℝ) (h₀ : d > 0) (h1 : (4 / 9) * d / (vf - vi) = 1) (v2 : d / (vf + ve) = 1.5) : (1 - 4 / 9) * d / (vi + ve) = 2.5 := by

  have h1' : (4 / 9) * d = (vf - vi) * 1 := by 
    field_simp [(show (vf - vi) ≠ 0 by
      by_contra h
      have h_eq : (4 / 9) * d / (vf - vi) = 0 := by
        rw [show (vf - vi) = 0 by linarith]
        norm_num
      linarith [h1, h_eq]
    )] at h1
    linarith
  have eq1 : (4 / 9) * d = (vf - vi) := by linarith

  have h2' : d = (vf + ve) * (1.5 : ℝ) := by 
    field_simp [(show (vf + ve) ≠ 0 by
      by_contra h
      have h_eq : d / (vf + ve) = 0 := by
        rw [show (vf + ve) = 0 by linarith]
        norm_num
      linarith [v2, h_eq]
    )] at v2
    ring_nf at v2 ⊢
    linarith

  have eq2 : (vf + ve) = (2 / 3) * d := by
    nlinarith

  have eq3 : (vi + ve) = (2 / 9) * d := by
    linarith

  have h3 : (1 - 4 / 9) * d = (5 / 9) * d := by
    ring_nf

  rw [h3]
  rw [eq3]

  have h4 : d ≠ 0 := by linarith
  field_simp [h4]
  <;> nlinarith
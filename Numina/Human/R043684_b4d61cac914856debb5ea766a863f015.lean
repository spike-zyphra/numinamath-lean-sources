import Mathlib

theorem algebra_198227 : {a : ℝ | a > -1 ∧ Real.logb 2 (a + 3) - Real.logb 2 (a + 1) = 1} = {1} := by
  ext a; simp
  constructor
  · rintro ⟨ha, h⟩
    have h1 : Real.logb 2 (a + 3) - Real.logb 2 (a + 1) = Real.logb 2 ((a + 3) / (a + 1)) := by
        rw [←Real.logb_div (by linarith) (by linarith)]
    rw [h1] at h
    have h2 : (a + 3) / (a + 1) = 2 := by
        have h_pos : (a + 3) / (a + 1) > 0 := by
            apply div_pos
            · linarith
            · linarith
        have h_eq : Real.logb 2 ((a + 3) / (a + 1)) = 1 := h
        rw [Real.logb_eq_iff_rpow_eq] at h_eq
        · -- $2^1 = (a+3)/(a+1)$
          linarith
        all_goals (try norm_num; try linarith)
    have h3 : a + 3 = 2 * (a + 1) := by
        have h2' : (a + 3) / (a + 1) = 2 := h2
        field_simp [(by linarith : a + 1 ≠ 0)] at h2'
        linarith
    linarith
  · intro ha
    rw [ha]
    norm_num
    rw [show Real.logb 2 4 = 2 by apply (Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num)).mpr (by norm_num)]
    linarith

import Mathlib

theorem algebra_97152 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 / (a + b + c) = 1)
    (h2 : 1 / (a + c) = 1.5)
    (h3 : 1 / (b + c) = 2) :
    1 / (a + b) = 1.2 := by
        have eq1 : a + b + c = 1 := by
            have h := h1
            field_simp [(show a + b + c ≠ 0 by nlinarith)] at h
            linarith

        have eq2 : a + c = 2 / 3 := by
            have h := h2
            field_simp [(show a + c ≠ 0 by nlinarith)] at h
            norm_num at h ⊢
            linarith

        have eq3 : b + c = 1 / 2 := by
            have h := h3
            field_simp [(show b + c ≠ 0 by nlinarith)] at h
            norm_num at h ⊢
            linarith

        have hb_eq : b = 1 / 3 := by
            nlinarith

        have ha2 : a = 1 / 2 := by
            nlinarith [hb_eq, eq2]

        have hab : a + b = 5 / 6 := by
            nlinarith [ha2, hb_eq]

        have hab2 : 1 / (a + b) = 6 / 5 := by
            rw [hab]
            norm_num

        rw [hab2]
        norm_num
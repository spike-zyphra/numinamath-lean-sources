import Mathlib
theorem algebra_604610 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 / (a + b + 2) + 1 / (b + c + 2) + 1 / (c + d + 2) + 1 / (d + a + 2) ≤ 1 := by

    have h1 : ∀ x y : ℝ, 0 < x → 0 < y → 1 / (x + y + 2) ≤ 1 / (2 * (√(x * y) + 1)) := by
        intro x y hx hy
        have h1 : x + y ≥ 2 * √(x * y):= by
            have g1 : (√x - √y) ^ 2 ≥ 0:= by positivity
            ring_nf at g1
            rw [show √x ^ 2 = x by refine Real.sq_sqrt (by linarith)] at g1
            rw [show √y ^ 2 = y by refine Real.sq_sqrt (by linarith)] at g1
            rw [show √x * √y = √(x * y) by refine Eq.symm (Real.sqrt_mul' x (by linarith))] at g1
            linarith
        have h2 : x + y + 2 ≥ 2 * (√(x * y) + 1):= by
            nlinarith [h1]
        have h3 : (x + y + 2) ≥ 2 * (√(x * y) + 1):= by linarith
        have h4 : (x + y + 2) > 0:= by positivity
        have h5 : 2 * (√(x * y) + 1) > 0:= by positivity
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h1]

    have h2 := h1 a b ha hb
    have h3 := h1 b c hb hc
    have h4 := h1 c d hc hd
    have h5 := h1 d a hd ha

    have h3' : 1 / (a + b + 2) + 1 / (c + d + 2) ≤ 1 / 2 := by
        have h6 : 1 / (a + b + 2) + 1 / (c + d + 2) ≤ 1 / (2 * (√(a * b) + 1)) + 1 / (2 * (√(c * d) + 1)) := by
            linarith only [h2, h4]
        have h7 : 1 / (2 * (√(a * b) + 1)) + 1 / (2 * (√(c * d) + 1)) = 1 / 2 := by
            have h4' : √(c * d) = 1 / √(a * b):= by
                rw [show c * d = 1 / (a * b) by
                  have h11 : a * b * c * d = 1 := h
                  have h22 : c * d = 1 / (a * b):= by
                    field_simp
                    nlinarith
                  linarith
                ]
                field_simp
            rw [h4']
            have h11 : √(a * b) > 0 := by
                positivity
            field_simp
            <;> nlinarith
        linarith [h6, h7]

    have h3'' : 1 / (b + c + 2) + 1 / (d + a + 2) ≤ 1 / 2 := by
        have h6 : 1 / (b + c + 2) + 1 / (d + a + 2) ≤ 1 / (2 * (√(b * c) + 1)) + 1 / (2 * (√(d * a) + 1)) := by
            linarith only [h3, h5]
        have h7 : 1 / (2 * (√(b * c) + 1)) + 1 / (2 * (√(d * a) + 1)) = 1 / 2 := by
            have h51 : √(d * a) = 1 / √(b * c):= by
                have h51 : d * a = 1 / (b * c):= by
                    have h51 : a * b * c * d = 1 := h
                    have h33 : b * c * (a * d) = 1 := by
                        nlinarith
                    have h44 : d * a = 1 / (b * c):= by
                        field_simp
                        nlinarith
                    linarith
                rw [h51]
                field_simp
            rw [h51]
            have h11 : √(b * c) > 0 := by
                positivity
            field_simp
            <;> nlinarith
        linarith [h6, h7]

    have h8 : 1 / (a + b + 2) + 1 / (b + c + 2) + 1 / (c + d + 2) + 1 / (d + a + 2) = (1 / (a + b + 2) + 1 / (c + d + 2)) + (1 / (b + c + 2) + 1 / (d + a + 2)) := by ring
    rw [h8]
    linarith only [h3', h3'']
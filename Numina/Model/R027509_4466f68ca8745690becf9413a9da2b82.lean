import Mathlib

theorem number_theory_228155 (a b c d : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : ∃ x y, a = x^2 - y^2 ∧ 0 < x ∧ 0 < y) (h2 : ∃ x y, b = x^2 - y^2 ∧ 0 < x ∧ 0 < y)
    (h3 : ∃ x y, c = x^2 - y^2 ∧ 0 < x ∧ 0 < y) (h4 : ∃ x y, d = x^2 - y^2 ∧ 0 < x ∧ 0 < y) :
    ∃ x y, a * b * c * d = x^2 - y^2 ∧ 0 < x ∧ 0 < y := by 
  rcases h1 with ⟨x1, y1, ha_eq, hx1_pos, hy1_pos⟩
  rcases h2 with ⟨x2, y2, hb_eq, hx2_pos, hy2_pos⟩
  rcases h3 with ⟨x3, y3, hc_eq, hx3_pos, hy3_pos⟩
  rcases h4 with ⟨x4, y4, hd_eq, hx4_pos, hy4_pos⟩

  use (x1 * x2 + y1 * y2) * (x3 * x4 + y3 * y4) + (x1 * y2 + y1 * x2) * (x3 * y4 + y3 * x4)
  use (x1 * x2 + y1 * y2) * (x3 * y4 + y3 * x4) + (x1 * y2 + y1 * x2) * (x3 * x4 + y3 * y4)

  rw [ha_eq, hb_eq, hc_eq, hd_eq]
  constructor
  · -- Show a * b * c * d = X^2 - Y^2
    nlinarith [sq_nonneg (x1 * x2 - y1 * y2), sq_nonneg (x3 * x4 - y3 * y4), 
        sq_nonneg (x1 * y2 - y1 * x2), sq_nonneg (x3 * y4 - y3 * x4), 
        sq_nonneg (x1 * x2 + y1 * y2), sq_nonneg (x3 * x4 + y3 * y4), 
        sq_nonneg (x1 * y2 + y1 * x2), sq_nonneg (x3 * y4 + y3 * x4), 
        mul_pos hx1_pos hy1_pos, mul_pos hx2_pos hy2_pos, 
        mul_pos hx3_pos hy3_pos, mul_pos hx4_pos hy4_pos
        ]
  constructor
  · -- Show 0 < x 
    nlinarith [mul_pos hx1_pos hx2_pos, mul_pos hx1_pos hy2_pos, 
                mul_pos hy1_pos hx2_pos, mul_pos hy1_pos hy2_pos, 
                mul_pos hx3_pos hx4_pos, mul_pos hx3_pos hy4_pos, 
                mul_pos hy3_pos hx4_pos, mul_pos hy3_pos hy4_pos, 
                mul_pos hx1_pos hy1_pos, mul_pos hx2_pos hy2_pos, 
                mul_pos hx3_pos hy3_pos, mul_pos hx4_pos hy4_pos
                ]
  · -- Show 0 < y 
    nlinarith [mul_pos hx1_pos hx2_pos, mul_pos hx1_pos hy2_pos, 
                mul_pos hy1_pos hx2_pos, mul_pos hy1_pos hy2_pos, 
                mul_pos hx3_pos hx4_pos, mul_pos hx3_pos hy4_pos, 
                mul_pos hy3_pos hx4_pos, mul_pos hy3_pos hy4_pos, 
                mul_pos hx1_pos hy1_pos, mul_pos hx2_pos hy2_pos, 
                mul_pos hx3_pos hy3_pos, mul_pos hx4_pos hy4_pos
                ]
import Mathlib

theorem algebra_305088 {p q : ℝ} {x1 x2 a b : ℝ}
    (h : x1 < x2) (hx1 : x1 > 1) (hx2 : x2 < 2)
    (h1 : x1^2 + p * x1 + q = 0) (h2 : x2^2 + p * x2 + q = 0)
    (ha : 1^2 + p * 1 + q = a) (hb : 2^2 + p * 2 + q = b) :
    (x1 = 1.4 ∧ x2 = 1.6 → a > 0 ∧ b > 0 ∧ a < 0.25 ∧ b < 0.25) ∧
    (a ≥ 0.25 → b < 0.25) := by
  have hp : p = -(x1 + x2) := by
    have eq1 : x1^2 + p * x1 + q = 0 := h1
    have eq2 : x2^2 + p * x2 + q = 0 := h2
    have eq3 : x1^2 + p * x1 + q - (x2^2 + p * x2 + q) = 0 := by linarith
    have eq4 : (x1 - x2) * (x1 + x2 + p) = 0 := by
      ring_nf at eq3 ⊢
      linarith
    cases' (mul_eq_zero.mp eq4) with h3 h4
    · -- x1 - x2 = 0, but x1 < x2, so impossible
      exfalso
      linarith
    · -- x1 + x2 + p = 0
      linarith
  have hq : q = x1 * x2 := by 
    rw [hp] at h1
    nlinarith [sq_pos_of_pos (show x1 - 1 > 0 by linarith)]
  have eq_a : a = 1 - (x1 + x2) + x1 * x2 := by
    have eq1 : (1:ℝ)^2 + p * (1:ℝ) + q = a := by linarith [ha]
    rw [hp, hq] at eq1 
    linarith
  have eq_b : b = 4 - 2 * (x1 + x2) + x1 * x2 := by
    have eq2 : (2:ℝ)^2 + p * (2:ℝ) + q = b := by linarith [hb]
    rw [hp, hq] at eq2 
    linarith
  constructor
  · -- Proof of the first implication: If x1 = 1.4 and x2 = 1.6, then a and b are positive and less than 0.25
    intro h_eq
    rcases h_eq with ⟨hx1_eq, hx2_eq⟩
    rw [hx1_eq, hx2_eq] at eq_a eq_b
    constructor
    · -- Show a > 0
      rw [eq_a]
      norm_num
    constructor
    · -- Show b > 0
      rw [eq_b]
      norm_num
    constructor
    · -- Show a < 0.25
      rw [eq_a]
      norm_num
    · -- Show b < 0.25
      rw [eq_b]
      norm_num
  · -- Proof of the second implication: If a >= 0.25, then b < 0.25
    intro h_eq 
    have h_eq' : 1 - (x1 + x2) + x1 * x2 ≥ 0.25 := by 
      linarith [eq_a, h_eq
      ]
    have h4 : 4 - 2 * (x1 + x2) + x1 * x2 < 0.25 := by
      nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x1 - 1.5), sq_nonneg (x2 - 1.5), 
        mul_pos (sub_pos.mpr hx1) (sub_pos.mpr (show (2 - x2 : ℝ) > 0 by linarith)), 
        mul_pos (sub_pos.mpr (show x2 - x1 > 0 by linarith)) (sub_pos.mpr (show 2 - x2 > 0 by linarith)), 
        sq_pos_of_pos (show x1 - 1 > 0 by linarith), 
        sq_pos_of_pos (show 2 - x2 > 0 by linarith)
      ]
    linarith [eq_b, h4]
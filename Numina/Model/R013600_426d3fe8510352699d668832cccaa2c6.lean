import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_164324 {x y : ℝ} (hx : 0 < y) (hy : y < x) (hxy : x * y = 1) :
    IsLeast {z | ∃ x y : ℝ, 0 < y ∧ y < x ∧ x * y = 1 ∧ z = (x ^ 2 + y ^ 2) / (x - y)} (2 * sqrt 2) := by
  constructor
  · -- Show 2 * sqrt(2) is in the set, using specific x and y
    use (Real.sqrt 2 + Real.sqrt 6) / 2, ( - Real.sqrt 2 + Real.sqrt 6) / 2
    constructor
    · -- Show that $0 < (- \sqrt{2} + \sqrt{6}) / 2$
      have h1 : -Real.sqrt 2 + Real.sqrt 6 > 0 := by
        have h6 : Real.sqrt 6 > Real.sqrt 2 := by
          apply Real.sqrt_lt_sqrt
          all_goals norm_num
        linarith
      linarith
    constructor
    · -- Show that $(- \sqrt{2} + \sqrt{6}) / 2 < (\sqrt{2} + \sqrt{6}) / 2$
      have h1 : (-Real.sqrt 2 + Real.sqrt 6) / 2 < (Real.sqrt 2 + Real.sqrt 6) / 2 := by 
        linarith [show Real.sqrt 2 > (0 : ℝ) by positivity] 
      linarith
    constructor
    · -- Show that $x * y = 1$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), 
      Real.sqrt_pos.mpr (show (0 : ℝ) < (6 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
      sq_nonneg (Real.sqrt 2 ^ 2 - 2),
      sq_nonneg (Real.sqrt 6 ^ 2 - 6),
      Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
      sq_nonneg (Real.sqrt 2 - Real.sqrt 6)]
    · -- Show that $2 * \sqrt(2) = \ldots$
      have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
      field_simp [(show Real.sqrt 2 > 0 by positivity), 
        (show Real.sqrt 6 > 0 by positivity), 
          show Real.sqrt 2 < Real.sqrt 6 by 
            apply Real.sqrt_lt_sqrt 
            all_goals norm_num
          ]
      <;> nlinarith [show Real.sqrt 2 > 0 by positivity, 
        Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), 
            Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, 
              Real.mul_self_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
                Real.mul_self_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num),
                  sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (Real.sqrt 6 ^ 2 - 6)
                ]
  · -- Show that $2 * \sqrt(2)$ is the minimum
    intro z hz
    rcases hz with ⟨x, y, hy_pos, h_lt, hxy, h_eq⟩
    have h1 : x ^ 2 + y ^ 2 = (x - y) ^ 2 + 2 := by
      have h2 : x * y = 1 := hxy
      nlinarith 
    have h2 : (x ^ 2 + y ^ 2) / (x - y) = (x - y) + 2 / (x - y) := by
      have h1' : x ^ 2 + y ^ 2 = (x - y) ^ 2 + 2 := h1 
      have h3 : x - y > 0 := by linarith 
      field_simp [h3]
      <;> nlinarith 
    have h5 : (x ^ 2 + y ^ 2) / (x - y) ≥ 2 * Real.sqrt 2 := by 
      rw [h2]
      have h6 : (x - y) > 0 := by 
        linarith 
      have h7 : (x - y) + 2 / (x - y) - 2 * Real.sqrt 2 ≥ 0 := by 
        have h8 : (x - y) > 0 := h6 
        have h11 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) 
        have h9 : (x - y) + 2 / (x - y) - 2 * Real.sqrt 2 = 
          ((x - y) ^ 2 + 2 - 2 * Real.sqrt 2 * (x - y)) / (x - y) := by 
            field_simp [h6] 
            <;> ring 
        rw [h9] 
        apply div_nonneg 
        · -- Show that $((x - y) ^ 2 + 2 - 2 * Real.sqrt 2 * (x - y)) \ge 0$ 
          have h10 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) 
          nlinarith [sq_nonneg ((x - y) - Real.sqrt 2), 
            Real.sqrt_nonneg 2, 
              sq_nonneg (Real.sqrt 2 ^ 2 - (2 : ℝ)), 
                sq_nonneg ((x - y) ^ 2 - 2)
            ]
        · -- Show that $x - y \ge 0$ 
          linarith 
      linarith 
    have h5' : z = (x^2 + y^2) / (x - y) := by
      linarith 
    linarith [h5, h5']
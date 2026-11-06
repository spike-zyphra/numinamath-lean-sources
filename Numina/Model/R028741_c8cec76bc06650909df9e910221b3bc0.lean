import Mathlib

theorem inequalities_157656 (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h :  c < a + b) (h' : b < a + c) (h'' : a < b + c) :
  3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) ∧
  a / (b + c) + b / (a + c) + c / (a + b) < 3
  := by
  constructor
  · -- Prove 3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b)
    have h1 : a / (b + c) + b / (a + c) + c / (a + b) ≥ 3 / 2 := by
      have h1 : 0 < (b + c) * (a + c) * (a + b) := by positivity
      have h2 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 ≥ 0 := by
        have eq1 : a / (b + c) + b / (a + c) + c / (a + b) - 3 / 2 =
              ( (a) * (a + c) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (a + c) - (3 / 2) * (b + c) * (a + c) * (a + b) ) / ( (b + c) * (a + c) * (a + b) ) := by
          field_simp
          ring
        rw [eq1]
        apply div_nonneg
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a - b + c), sq_nonneg (-a + b + c),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
        positivity
      linarith
    linarith
  · -- Prove a / (b + c) + b / (a + c) + c / (a + b) < 3
    have h5 : a / (b + c) < 1 := by
      have h8 : b + c > a := by linarith [h'']
      apply (div_lt_iff₀ (by linarith)).mpr
      nlinarith
    have h6 : b / (a + c) < 1 := by
      have h9 : a + c > b := by linarith [h']
      apply (div_lt_iff₀ (by linarith)).mpr
      nlinarith
    have h7 : c / (a + b) < 1 := by
      have h10 : a + b > c := by linarith [h]
      apply (div_lt_iff₀ (by linarith)).mpr
      nlinarith
    linarith [h5, h6, h7]
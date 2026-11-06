import Mathlib


open Real


lemma lemma_1 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) :
    8 * u * v * w ≤ (u + v) * (v + w) * (w + u) := by
  nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u),
          sq_nonneg (u + v - w), sq_nonneg (u + w - v), sq_nonneg (v + w - u),
          mul_pos hu hv, mul_pos hv hw, mul_pos hw hu,
          mul_pos (show 0 < u + v by linarith) (show 0 < v + w by linarith),
          mul_pos (show 0 < v + w by linarith) (show 0 < w + u by linarith),
          mul_pos (show 0 < u + v by linarith) (show 0 < w + u by linarith)
          ]

lemma lemma_2 (u v w : ℝ) (hu : 0 < u) (hv : 0 < v) (hw : 0 < w)
    (h : u + v + w = 1) : 8 * u * v * w ≤ (1 - u) * (1 - v) * (1 - w) := by
  have h1 : 1 - u = v + w := by linarith
  have h2 : 1 - v = u + w := by linarith
  have h3 : 1 - w = u + v := by linarith
  have h4 : (1 - u) * (1 - v) * (1 - w) = (v + w) * (u + w) * (u + v) := by
    rw [h1, h2, h3]
    <;> nlinarith [sq_nonneg (u - v), sq_nonneg (u - w), sq_nonneg (v - w), mul_pos hu hv, mul_pos hu hw, mul_pos hv hw]
  rw [h4]
  nlinarith [sq_nonneg (u * v - v * w), sq_nonneg (v * w - w * u), sq_nonneg (w * u - u * v),
          sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u),
          sq_nonneg (u * (u - v)), sq_nonneg (u * (u - w)),
          sq_nonneg (v * (v - u)), sq_nonneg (v * (v - w)),
          sq_nonneg (w * (w - u)), sq_nonneg (w * (w - v)),
          mul_pos hu hv, mul_pos hu hw, mul_pos hv hw]


theorem inequalities_602978
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 / (1 + a^2) + b^2 / (1 + b^2) + c^2 / (1 + c^2) = 1) :
    a * b * c ≤ Real.sqrt 2 / 4 := by
  have eq1 : a^2 / (1 + a^2) + b^2 / (1 + b^2) + c^2 / (1 + c^2) = 1 := h
  have eq2 : (a^2) * (1 + b^2) * (1 + c^2) + (b^2) * (1 + a^2) * (1 + c^2) + (c^2) * (1 + a^2) * (1 + b^2) = (1 + a^2) * (1 + b^2) * (1 + c^2) := by
    have pos1 : (1 + a^2) * (1 + b^2) * (1 + c^2) ≠ 0 := by positivity
    field_simp at eq1 ⊢
    nlinarith [sq_nonneg (a^2 * b^2), sq_nonneg (b^2 * c^2), sq_nonneg (c^2 * a^2), mul_pos (show 0 < a^2 by positivity) (show 0 < b^2 by positivity), mul_pos (show 0 < a^2 by positivity) (show 0 < c^2 by positivity), mul_pos (show 0 < b^2 by positivity) (show 0 < c^2 by positivity)]
  have h2 : a ^ 2 * b ^ 2 * c ^ 2 ≤ 1 / 8 := by
    nlinarith [sq_nonneg (a^2 - 1 / 2), sq_nonneg (b^2 - 1 / 2), sq_nonneg (c^2 - 1 / 2),
          sq_nonneg (a^2 * b^2 - 1 / 4), sq_nonneg (b^2 * c^2 - 1 / 4), sq_nonneg (c^2 * a^2 - 1 / 4),
          mul_pos (show 0 < a ^ 2 by positivity) (show 0 < b ^ 2 by positivity), mul_pos (show 0 < a ^ 2 by positivity) (show 0 < c ^ 2 by positivity), mul_pos (show 0 < b ^ 2 by positivity) (show 0 < c ^ 2 by positivity)]
  have h3 : (a * b * c) ^ 2 ≤ 1 / 8 := by
    have h4 : (a * b * c) ^ 2 = a^2 * b^2 * c^2 := by ring
    rw [h4]
    nlinarith
  have h4 : a * b * c ≤ Real.sqrt 2 / 4 := by
    have h5 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have h6 : (Real.sqrt 2 / 4 : ℝ) ^ 2 = 1 / 8 := by
      nlinarith
    have h7 : (a * b * c) ^ 2 ≤ (1 / 8 : ℝ) := h3
    have h8 : a * b * c ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, Real.sqrt_nonneg 2]
  linarith
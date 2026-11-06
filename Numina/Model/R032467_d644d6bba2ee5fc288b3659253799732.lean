import Mathlib


open Real


theorem inequalities_599946 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b + b * c + c * a = a * b * c) :
    1 ≤ (a^5 + b^5) / (a * b * (a^4 + b^4)) + (b^5 + c^5) / (b * c * (b^4 + c^4)) +
        (c^5 + a^5) / (c * a * (c^4 + a^4)) := by


  have lemma_1 : ∀ x y : ℝ, 0 < x → 0 < y → 2 * (x ^ 5 + y ^ 5) ≥ (x + y) * (x ^ 4 + y ^ 4) := by
    intro x y hx hy
    have h1 : 0 < x := hx
    have h2 : 0 < y := hy
    have h3 : x + y > 0 := by linarith
    have h4 : x ^ 2 + y ^ 2 > 0 := by nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg (x * y), mul_pos hx hy, sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x ^ 2 - y ^ 2)]


  have h1 : (a^5 + b^5) / (a * b * (a^4 + b^4)) ≥ (a + b) / (2 * a * b) := by
    have h2 : 0 < a * b := mul_pos ha hb
    have h3 : 0 < a ^ 4 + b ^ 4 := by positivity
    have h4 : 0 < a * b * (a^4 + b^4) := by positivity
    have h5 : 2 * (a ^ 5 + b ^ 5) ≥ (a + b) * (a ^ 4 + b ^ 4) := by
      apply lemma_1 a b ha hb
    have h6 : (a^5 + b^5) / (a * b * (a^4 + b^4)) ≥ (a + b) / (2 * a * b) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith


  have h2 : (b^5 + c^5) / (b * c * (b^4 + c^4)) ≥ (b + c) / (2 * b * c) := by
    have h3 : 0 < b * c := mul_pos hb hc
    have h4 : 0 < b ^ 4 + c ^ 4 := by positivity
    have h5 : 0 < b * c * (b^4 + c^4) := by positivity
    have h6 : 2 * (b ^ 5 + c ^ 5) ≥ (b + c) * (b ^ 4 + c ^ 4) := by
      apply lemma_1 b c hb hc
    have h7 : (b^5 + c^5) / (b * c * (b^4 + c^4)) ≥ (b + c) / (2 * b * c) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith


  have h3 : (c^5 + a^5) / (c * a * (c^4 + a^4)) ≥ (c + a) / (2 * c * a) := by
    have h4 : 0 < c * a := mul_pos hc ha
    have h5 : 0 < c ^ 4 + a ^ 4 := by positivity
    have h6 : 0 < c * a * (c^4 + a^4) := by positivity
    have h7 : 2 * (c ^ 5 + a ^ 5) ≥ (c + a) * (c ^ 4 + a ^ 4) := by
      apply lemma_1 c a hc ha
    have h8 : (c^5 + a^5) / (c * a * (c^4 + a^4)) ≥ (c + a) / (2 * c * a) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    linarith


  have h4 : (a^5 + b^5) / (a * b * (a^4 + b^4)) + (b^5 + c^5) / (b * c * (b^4 + c^4)) + (c^5 + a^5) / (c * a * (c^4 + a^4)) ≥ (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) := by
    linarith [h1, h2, h3]


  have h5 : (a + b) / (2 * a * b) + (b + c) / (2 * b * c) + (c + a) / (2 * c * a) = 1 / a + 1 / b + 1 / c := by
    field_simp
    ring


  have h6 : 1 / a + 1 / b + 1 / c = 1 := by
    field_simp at h ⊢
    nlinarith


  linarith [h4, h5, h6]
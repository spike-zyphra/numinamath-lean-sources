import Mathlib

theorem algebra_124883 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 2 + b * x + c) (hzeros : ∃ x, f x = 0) :
    min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ 5 / 4 := by
  rcases hzeros with ⟨x, hx⟩
  rw [hf] at hx
  have h1 : a * x ^ 2 + b * x + c = 0 := by
    simpa using hx
  have h2 : b ^ 2 ≥ 4 * a * c := by
    have h1' : a * x ^ 2 + b * x + c = 0 := h1
    have eq1 : 4 * a * c = -4 * a ^ 2 * x ^ 2 - 4 * a * b * x := by 
      have eq2 : c = -a * x^2 - b * x := by
        nlinarith
      rw [eq2]
      ring_nf
    nlinarith [sq_nonneg (2 * a * x + b), sq_nonneg (a * x + b / 2), sq_nonneg (x * a + b / 2), sq_nonneg (x * b + a * c), sq_nonneg (x * (2 * a * x + b))]
  by_contra h
  push_neg at h
  have h3 : (b + c) / a > 5 / 4 := by
    by_contra h4
    push_neg at h4
    have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ 5 / 4 := by
      have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ (b + c) / a := by
        simp [min_le_iff]
      nlinarith
    linarith
  have h4 : (c + a) / b > 5 / 4 := by
    by_contra h5
    push_neg at h5
    have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ 5 / 4 := by
      have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ (c + a) / b := by
        simp [min_le_iff]
      nlinarith
    linarith
  have h5 : (a + b) / c > 5 / 4 := by
    by_contra h6
    push_neg at h6
    have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ 5 / 4 := by
      have : min (min ((b + c) / a) ((c + a) / b)) ((a + b) / c) ≤ (a + b) / c := by
        simp [min_le_iff]
      nlinarith
    linarith
  have h6 : 4 * (b + c) > 5 * a := by
    have h7 : 0 < a := by linarith
    have h8 : (b + c) / a > 5 / 4 := h3
    have h9 : (b + c) / a > 5 / 4 := h3
    have h10 : 4 * (b + c) > 5 * a := by
      have h7 : 0 < a := by nlinarith
      apply (lt_div_iff' (by linarith)).mp at h9
      linarith
    linarith
  have h7 : 4 * (c + a) > 5 * b := by
    have h7 : (c + a) / b > 5 / 4 := h4
    have h8 : 0 < b := by nlinarith
    have h9 : (c + a) / b > 5 / 4 := h7
    have h10 : 4 * (c + a) > 5 * b := by
      have h8 : 0 < b := by nlinarith
      apply (lt_div_iff' (by linarith)).mp at h9
      linarith
    linarith
  have h8 : 4 * (a + b) > 5 * c := by
    have h9 : (a + b) / c > 5 / 4 := h5
    have h11 : 0 < c := by nlinarith
    have h9 : (a + b) / c > 5 / 4 := h5
    have h12 : 4 * (a + b) > 5 * c := by
      have h11 : 0 < c := by nlinarith
      apply (lt_div_iff' (by linarith)).mp at h9
      linarith
    linarith
  nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (2 * a - b), sq_nonneg (2 * b - a - c), sq_nonneg (2 * c - a - b)]
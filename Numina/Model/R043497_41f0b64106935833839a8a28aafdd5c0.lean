import Mathlib

theorem algebra_300072 {f: ℝ → ℝ} {a b c p1 p2 m1 m2 : ℝ} (ha : a > b) (hb : b > c)
  (hf: ∀x:ℝ, f x = a*x^2+b*x+c)
  (hf2: f 2 = 0) (hfm1: f m1 = p1)(hfm2: f m2 = p2)
  (h1: p1*p2 - c*p1 + a*p2 - a*c = 0):
  f (m1 + 5) > 0 ∨ f (m2 + 5) > 0 := by
  have eq1 : a * 4 + b * 2 + c = 0 := by
    rw [hf 2] at hf2
    ring_nf at hf2 ⊢
    linarith
  -- Express the function at m1 and m2 using polynomial expressions
  have eq2 : a * m1 ^ 2 + b * m1 + c = p1 := by
    rw [hf m1] at hfm1
    linarith
  have eq3 : a * m2 ^ 2 + b * m2 + c = p2 := by
    rw [hf m2] at hfm2
    linarith
  -- From hypothesis p1*p2 - c*p1 + a*p2 - a*c = 0 we show it is equivalent to (p1 + a)(p2 - c) = 0
  have h2 : (p1 + a) * (p2 - c) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case 1: p1 + a = 0
    have hp1 : p1 = -a := by linarith
    have eq4 : a * m1 ^ 2 + b * m1 + c = -a := by linarith [eq2, hp1]
    by_contra h
    push_neg at h
    have h11 : f (m1 + 5) ≤ 0 := by linarith [h.1]
    have h12 : f (m2 + 5) ≤ 0 := by linarith [h.2]
    rw [hf (m1 + 5)] at h11
    rw [hf (m2 + 5)] at h12
    nlinarith [sq_nonneg (m1 + 5), sq_nonneg (m2 + 5), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (m1 + 1), sq_nonneg (m2 + 1), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]
  · -- Case 2: p2 - c = 0
    have hp2 : p2 = c := by linarith
    have eq4 : a * m2 ^ 2 + b * m2 = 0 := by
      nlinarith [eq3, hp2]
    by_contra h
    push_neg at h
    have h11 : f (m1 + 5) ≤ 0 := by linarith [h.1]
    have h12 : f (m2 + 5) ≤ 0 := by linarith [h.2]
    rw [hf (m1 + 5)] at h11
    rw [hf (m2 + 5)] at h12
    nlinarith [sq_nonneg (m1 + 5), sq_nonneg (m2 + 5), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (m1 - m2), sq_nonneg (a - c), sq_nonneg (m1 * a), sq_nonneg (m2 * a), sq_nonneg ((m1 + 5) - 2), sq_nonneg ((m2 + 5) - 2), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]
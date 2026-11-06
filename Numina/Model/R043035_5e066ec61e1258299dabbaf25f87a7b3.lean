import Mathlib

theorem algebra_230310 (a b c d e f g h : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hg' : 0 < h)
    (h1 : a * b = c * d) (h2 : b * c = d * e) (h3 : c * d = e * f)
    (h4 : d * e = e * g) (h5 : e * f = f * h) (h6 : f * g = g * h)
    (h7 : g * h = a * b) (h8 : a * b = 720) :
    n = 6 := by
-- From h9 : g * h = 720
  have h9 : g * h = 720 := by
    linarith [h7, h8]
  -- From h4 : d * e = e * g. Since `e ≠ 0`, we can divide by e to get `d = g`.
  have h10 : d = g := by
    have h11 : e > 0 := he
    have h12 : d * e = e * g := by linarith [h4]
    have h13 : d = g := by
      apply (mul_left_inj' (ne_of_gt he)).mp
      linarith
    linarith
  -- From h6 : f * g = g * h. Since `g ≠ 0`, we can divide by g to get `f = h`.
  have h14 : f = h := by
    have h15 : g > 0 := hg
    have h16 : f * g = g * h := by linarith [h6]
    have h17 : f = h := by
      apply (mul_left_inj' (ne_of_gt hg)).mp
      linarith
    linarith
  -- From h5 : e * f = f * h. Substitute `f = h`. So `e * h = h * h`.
  -- Since `h ≠ 0` (from hg'), we can divide by h to get `e = h`.
  have h18 : e = h := by
    have h19 : f = h := h14
    rw [h19] at h5
    have h20 : h > 0 := hg'
    have h21 : e = h := by
      apply (mul_right_inj' (ne_of_gt h20)).mp
      linarith
    linarith
  -- From h3 : c * d = e * f. Substitute `d = g` and `e = f = h`. So we get `c * g = h * h`.
  have h22 : c * g = h * h := by
    rw [show d = g by linarith [h10]] at h3
    rw [show e = h by linarith [h18]] at h3
    rw [show f = h by linarith [h14]] at h3
    linarith
  -- From h8 : a * b = 720.
  have h26 : a * b = 720 := h8
  -- From h22 : c * g = h * h.
  have h27 : c * g = h * h := h22
  -- From h27 : c * g = h * h. From h1 : a * b = c * d. Substitute d = g to get a * b = c * g.
  have h25 : a * b = c * g := by
    rw [show d = g by linarith [h10]] at h1
    linarith
  -- From h25 and h27: a * b = h * h.
  have h28 : a * b = h * h := by
    linarith [h25, h27]
  -- Since a * b = 720, h * h = 720.
  have h29 : h * h = 720 := by
    nlinarith [h26, h28]
  -- Now, we have `h * h = 720` and h > 0.
  -- 720 isn't a perfect square, contradiction.
  have h30 : h ≤ 28 := by
    by_contra h31
    push_neg at h31
    have h32 : h * h ≥ 29 * 29 := by
      nlinarith [h31]
    nlinarith [h29]
  interval_cases h <;> omega
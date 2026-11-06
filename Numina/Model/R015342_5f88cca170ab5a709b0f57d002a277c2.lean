import Mathlib

theorem algebra_309294 {a b c d : ℤ} (ha : Even a) (hb : Even b) (hc : Even c) (hd : Even d)
    (hord : 0 < a ∧ a < b ∧ b < c ∧ c < d) (hdiff : d - a = 90) (hseq1 : ∃ d, b = a + d ∧ c = b + d)
    (hseq2 : ∃ r, c = b * r ∧ d = c * r) :
    a + b + c + d = 194 := by
  rcases hseq1 with ⟨t, hab, hbc⟩
  rcases hseq2 with ⟨r, h1, h2⟩
  have h3 : a > 0 := hord.1
  have h4 : a < b := hord.2.1
  have h5 : b < c := hord.2.2.1
  have h6 : c < d := hord.2.2.2
  have h7 : b = a + t := by linarith
  have h8 : c = a + 2 * t := by
    linarith [hbc, h7]
  rw [show b = a + t by linarith [h7]] at h1
  rw [show c = a + 2 * t by linarith [h8]] at h1
  have h9 : a + 2 * t = r * (a + t) := by linarith
  have h11 : d = a + 90 := by linarith [hdiff]
  rw [show c = a + 2 * t by linarith [h8]] at h2
  rw [show d = a + 90 by linarith [hdiff]] at h2
  -- From h2: a + 90 = r * (a + 2 * t)
  -- From h9 and h2: deriving contradiction
  have h12 : r > 1 := by
    nlinarith [h3, h4, h7, h9, h6, h5]
  have h13 : r ≤ 2 := by
    nlinarith [h9, h3, h7, h4, h5, h6, h2, sq_pos_of_pos h3, sq_pos_of_pos (show t > 0 by nlinarith [h4, h7, h3]), sq_nonneg (t), sq_nonneg (r - 1)]
  have h14 : r = 2 := by
    nlinarith
  rw [h14] at h9
  -- From h9: a + 2t = 2(a + t)
  -- a + 2t = 2a + 2t
  -- 0 = a
  -- contradicts with h3: a > 0
  nlinarith
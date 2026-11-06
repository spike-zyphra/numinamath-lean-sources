import Mathlib


open Real


lemma lemma_1 (a b c x y z : ℝ)
    (ha : 0 < a) (hsum : a + b + c = x + y + z) (hprod : a * b * c = x * y * z)
    (hle : a ≤ x ∧ x < y ∧ y < z) :
    x * y + y * z + z * x ≤ a * b + b * c + c * a := by
  rcases hle with ⟨ha1, h1, h2⟩
  nlinarith [sq_nonneg (x - a), sq_nonneg (y - a), sq_nonneg (z - a),
    sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
    mul_nonneg (show 0 ≤ x - a by linarith) (show 0 ≤ y - x by linarith),
    mul_nonneg (show 0 ≤ y - x by linarith) (show 0 ≤ z - y by linarith),
    mul_nonneg (show 0 ≤ x - a by linarith) (show 0 ≤ z - y by linarith),
    mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < a + 1 by nlinarith)]


theorem algebra_607367 {a b c x y z : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
(hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h1 : a + b + c = x + y + z) (h2 : a * b * c = x * y * z)
(h3 : a ≤ x) (h4 : x < y) (h5 : y < z) (h6 : z ≤ c) (h7 : a < b) (h8 : b < c) :
a = x ∧ b = y ∧ c = z := by

  have h9 : x * y + y * z + z * x ≤ a * b + b * c + c * a := by
    have h10 : a ≤ x := h3
    have h11 : x < y := h4
    have h12 : y < z := h5
    apply lemma_1 a b c x y z ha (by linarith) (by linarith) ⟨h10, h11, h12⟩

  have h10 : a * b + b * c + c * a ≤ x * y + y * z + z * x := by
    nlinarith [sq_nonneg (x - a), sq_nonneg (y - b), sq_nonneg (z - c), 
      mul_nonneg (show 0 ≤ (x - a) by linarith) (show 0 ≤ (y - x) by linarith), 
      mul_nonneg (show 0 ≤ (y - x) by linarith) (show 0 ≤ (z - y) by linarith), 
      mul_nonneg (show 0 ≤ (x - a) by linarith) (show 0 ≤ (z - y) by linarith), 
      mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), 
      mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith), 
      mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith), 
      mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < z by linarith)]

  have h11 : a * b + b * c + c * a = x * y + y * z + z * x := by
    nlinarith

  have h32 : (a - x) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - x), sq_nonneg (b - y), sq_nonneg (c - z), 
      mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith), 
      mul_pos (show (0 : ℝ) < b by linarith) (show (0 : ℝ) < c by linarith), 
      mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < y by linarith), 
      mul_pos (show (0 : ℝ) < y by linarith) (show (0 : ℝ) < z by linarith)]

  have ha1 : a - x = 0 := by
    nlinarith [sq_nonneg (a - x)]

  have hax : a = x := by linarith

  have hb1 : b = y := by
    nlinarith [sq_nonneg (b - y), sq_nonneg (c - z), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith)]

  have hc1 : c = z := by
    nlinarith [sq_nonneg (c - z), sq_nonneg (b - y), mul_pos (show (0 : ℝ) < a by linarith) (show (0 : ℝ) < b by linarith)]

  exact ⟨hax, hb1, hc1⟩
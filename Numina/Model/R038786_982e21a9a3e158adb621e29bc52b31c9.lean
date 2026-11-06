import Mathlib

open Real


lemma lemma_1 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) = 1) :
    1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2) ≤ 3 / 4 := by
  have h1 : 0 < x + 1 := by linarith
  have h2 : 0 < y + 1 := by linarith
  have h3 : 0 < z + 1 := by linarith
  have h4 : 0 < x + 2 := by linarith
  have h5 : 0 < y + 2 := by linarith
  have h6 : 0 < z + 2 := by linarith
  have h7 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) = 1 := h
  have h8 : (y + 1) * (z + 1) + (x + 1) * (z + 1) + (x + 1) * (y + 1) = (x + 1) * (y + 1) * (z + 1) := by
    field_simp [(show x + 1 ≠ 0 by linarith), (show y + 1 ≠ 0 by linarith), (show z + 1 ≠ 0 by linarith)] at h7 ⊢
    nlinarith
  have h9 : 4 * ((y + 2) * (z + 2) + (x + 2) * (z + 2) + (x + 2) * (y + 2)) ≤ 3 * (x + 2) * (y + 2) * (z + 2) := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
      mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
    ]
  have h10 : 1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2) ≤ 3 / 4 := by
    have hx2 : 0 < (x + 2) * (y + 2) * (z + 2) := by positivity
    have h11 : (1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2)) - 3 / 4 ≤ 0 := by
      have h14 : (1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2)) - 3 / 4 =
          (4 * ((y + 2) * (z + 2) + (x + 2) * (z + 2) + (x + 2) * (y + 2)) - 3 * (x + 2) * (y + 2) * (z + 2) ) / (4 * (x + 2) * (y + 2) * (z + 2)) := by
        field_simp [(show x + 2 ≠ 0 by linarith), (show y + 2 ≠ 0 by linarith), (show z + 2 ≠ 0 by linarith)]
        ring
      rw [h14]
      apply div_nonpos_of_nonpos_of_nonneg
      .
        nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
        ]
      all_goals positivity
    linarith
  exact h10


theorem inequalities_87166 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h1 : a ^ x = b * c) (h2 : b ^ y = c * a)
    (h3 : c ^ z = a * b) :
    1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) ≤ 3 / 4 := by

  have ha1 : 0 < a := ha.1
  have ha2 : a < 1 := ha.2
  have hb1 : 0 < b := hb.1
  have hb2 : b < 1 := hb.2
  have hc1 : 0 < c := hc.1
  have hc2 : c < 1 := hc.2

  have eq1 : x * (log a) = log b + log c := by
    have h1' : a ^ x = b * c := h1
    have h11 : log (a ^ x) = log (b * c) := by
      rw [h1']
    have h12 : log (a ^ x) = x * (log a) := by
      rw [log_rpow]
      all_goals linarith
    have h13 : log (b * c) = log b + log c := by
      rw [log_mul (by linarith) (by linarith)]
    rw [h12, h13] at h11
    linarith

  have eq2 : y * (log b) = log c + log a := by
    have h2' : b ^ y = c * a := h2
    have h21 : log (b ^ y) = log (c * a) := by
      rw [h2']
    have h22 : log (b ^ y) = y * (log b) := by
      rw [log_rpow]
      all_goals linarith
    have h23 : log (c * a) = log c + log a := by
      rw [log_mul (by linarith) (by linarith)]
    rw [h22, h23] at h21
    linarith

  have eq3 : z * (log c) = log a + log b := by
    have h3' : c ^ z = a * b := h3
    have h31 : log (c ^ z) = log (a * b) := by
      rw [h3']
    have h32 : log (c ^ z) = z * (log c) := by
      rw [log_rpow]
      all_goals linarith
    have h33 : log (a * b) = log a + log b := by
      rw [log_mul (by linarith) (by linarith)]
    rw [h32, h33] at h31
    linarith

  have eq4 : 1 / (x + 1) + 1 / (y + 1) + 1 / (z + 1) = 1 := by
    have hx2 : log a < 0 := by
      have h41 : log a < log (1 : ℝ) := by
        apply Real.log_lt_log
        all_goals linarith
      have h42 : log (1 : ℝ) = 0 := by
        simp [log_one]
      linarith
    have hy2 : log b < 0 := by
      have h41 : log b < log (1 : ℝ) := by
        apply Real.log_lt_log
        all_goals linarith
      have h42 : log (1 : ℝ) = 0 := by
        simp [log_one]
      linarith
    have hz2 : log c < 0 := by
      have h41 : log c < log (1 : ℝ) := by
        apply Real.log_lt_log
        all_goals linarith
      have h42 : log (1 : ℝ) = 0 := by
        simp [log_one]
      linarith
    field_simp [(show x + 1 ≠ 0 by linarith), (show y + 1 ≠ 0 by linarith), (show z + 1 ≠ 0 by linarith)]
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (log a - log b), sq_nonneg (log b - log c), sq_nonneg (log c - log a),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
          mul_pos (show 0 < (1 - a) by linarith) (show 0 < (1 - b) by linarith),
          mul_pos (show 0 < (1 - b) by linarith) (show 0 < (1 - c) by linarith),
          mul_pos (show 0 < (1 - c) by linarith) (show 0 < (1 - a) by linarith),
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith),
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith),
          mul_pos (show 0 < c by linarith) (show 0 < a by linarith)
         ]
  have h6 : 1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2) ≤ 3 / 4 := by
    have h7 : 1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2) ≤ 3 / 4 := by
      apply lemma_1 x y z (by linarith) (by linarith) (by linarith) (eq4)
    linarith
  have hx5 : 1 / (2 + x) + 1 / (2 + y) + 1 / (2 + z) = 1 / (x + 2) + 1 / (y + 2) + 1 / (z + 2) := by
    ring_nf
  rw [hx5]
  linarith
import Mathlib

open Real
open scoped BigOperators

theorem inequalities_160046 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (s : ℝ) (hs : s = (a + b + c) / 2) :
  9 / s ≤ 1 / (s - a) + 1 / (s - b) + 1 / (s - c) := by
  have ha1 : s - a > 0 := by
    rw [hs]
    nlinarith
  have hb1 : s - b > 0 := by
    rw [hs]
    nlinarith
  have hc1 : s - c > 0 := by
    rw [hs]
    nlinarith
  have h1 : s > 0 := by
    rw [hs]
    linarith
  have h3 : 1 / (s - a) + 1 / (s - b) + 1 / (s - c) - 9 / s ≥ 0 := by
    have h4 : s > 0 := h1
    have h5 : s - a > 0 := ha1
    have h6 : s - b > 0 := hb1
    have h7 : s - c > 0 := hc1
    have h4 : 0 < s * (s - a) * (s - b) * (s - c) := by positivity
    have h9 : 1 / (s - a) + 1 / (s - b) + 1 / (s - c) - 9 / s =
        (s * (s - b) * (s - c) + s * (s - a) * (s - c) + s * (s - a) * (s - b) - 9 * (s - a) * (s - b) * (s - c)) / (s * (s - a) * (s - b) * (s - c)) := by
      field_simp
      <;> ring
      <;> field_simp
      <;> ring_nf <;> field_simp
      <;> ring
    rw [h9] at *
    apply div_nonneg
    · -- Numerator must be positive
      nlinarith [sq_nonneg (s - a - s + b), sq_nonneg (s - a - s + c), sq_nonneg (s - b - s + c), 
          mul_pos (show 0 < s - a by linarith) (show 0 < s - b by linarith), 
          mul_pos (show 0 < s - a by linarith) (show 0 < s - c by linarith), 
          mul_pos (show 0 < s - b by linarith) (show 0 < s - c by linarith), 
          h1
        ]
    · -- Denominator must be positive
      positivity
  linarith
  all_goals linarith
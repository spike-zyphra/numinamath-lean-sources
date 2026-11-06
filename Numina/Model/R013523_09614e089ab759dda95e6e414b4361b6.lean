import Mathlib

open Real
open scoped BigOperators

theorem inequalities_142862 (k : ℝ) :
  (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a + b > c → b + c > a → c + a > b →
    (b * c / (b + c - a) + a * c / (a + c - b) + a * b / (a + b - c)) ≥
    k * (a + b + c)) ↔ k ≤ 1 :=
by
  constructor
  · -- Assume the inequality holds for all positive real numbers, prove that k ≤ 1.
    intro h
    have h1 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1
    linarith
  · -- Now prove the reverse: if k ≤ 1, then the inequality holds for all positive real numbers.
    intro hk a b c ha hb hc h1 h2 h3
    have h4 : b + c - a > 0 := by linarith
    have h5 : a + c - b > 0 := by linarith
    have h6 : a + b - c > 0 := by linarith
    have h7 : (b * c / (b + c - a) + a * c / (a + c - b) + a * b / (a + b - c)) ≥ (a + b + c) := by
      have h8 : b + c - a > 0 := by linarith
      have h9 : a + c - b > 0 := by linarith
      have h10 : a + b - c > 0 := by linarith
      have h11 : b * c / (b + c - a) + a * c / (a + c - b) + a * b / (a + b - c) - (a + b + c) ≥ 0 := by
        have h8 : b + c - a > 0 := by linarith
        have h9 : a + c - b > 0 := by linarith
        have h10 : a + b - c > 0 := by linarith
        have h12 : (b * c / (b + c - a) + a * c / (a + c - b) + a * b / (a + b - c) - (a + b + c)) =
            (b * c * (a + c - b) * (a + b - c) + a * c * (b + c - a) * (a + b - c) + a * b * (b + c - a) * (a + c - b) - (a + b + c) * (b + c - a) * (a + c - b) * (a + b - c)) / ((b + c - a) * (a + c - b) * (a + b - c)) := by
          field_simp
          <;> ring
        rw [h12]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
          sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show b + c - a > 0 by linarith) (show a + c - b > 0 by linarith),
          mul_pos (show a + c - b > 0 by linarith) (show a + b - c > 0 by linarith),
          mul_pos (show b + c - a > 0 by linarith) (show a + b - c > 0 by linarith)]
        positivity
      linarith
    have h8 : (a + b + c) ≥ k * (a + b + c) := by
      have h9 : (a + b + c) > 0 := by
        nlinarith
      nlinarith [show k ≤ 1 by linarith, show k ≤ 1 by linarith]
    linarith [h7, h8]
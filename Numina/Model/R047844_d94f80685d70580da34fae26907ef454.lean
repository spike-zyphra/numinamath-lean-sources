import Mathlib

open Real Set

theorem algebra_386 (A : ℝ → ℝ → ℝ → ℝ)
    (hA : A = fun a b c => a * b + b * c + c * a - 2 * a * b * c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    A a b c ≤ 7 / 27 ∧ A a b c ≥ -1 / 27 := by
  have h1 : c = 1 - a - b := by linarith
  have h2 : A a b c = a * b + b * c + c * a - 2 * a * b * c := by simp [hA]
  rw [h2]
  constructor
  · -- Show that A a b c ≤ 7/27
    have h3 : a * b + b * c + c * a - 2 * a * b * c ≤ 7/27 := by
      have h4 : c = 1 - a - b := by linarith
      rw [h4]
      have h5 : a * b + b * (1 - a - b) + (1 - a - b) * a - 2 * a * b * (1 - a - b) ≤ 7/27 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            sq_nonneg (a + b - (1 - a - b)), sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ((1 - a - b) - 1/3), 
            mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), 
            mul_pos hb (show 0 < 1 - a - b by nlinarith),
            mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
            sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), 
            sq_nonneg (a * b - (1 - a - b) * a), sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b))
            ]
      linarith
    linarith
  · -- Show that A a b c ≥ -1/27
    have h3 : a * b + b * c + c * a - 2 * a * b * c ≥ -1/27 := by
      have h4 : c = 1 - a - b := by linarith
      rw [h4]
      have h5 : a * b + b * (1 - a - b) + (1 - a - b) * a - 2 * a * b * (1 - a - b) ≥ -1/27 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b)), 
            sq_nonneg (a + b - (1 - a - b)), sq_nonneg (a - 1/3), sq_nonneg (b - 1/3), sq_nonneg ((1 - a - b) - 1/3), 
            mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), 
            mul_pos hb (show 0 < 1 - a - b by nlinarith),
            mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
            sq_nonneg (a * b - b * (1 - a - b)), sq_nonneg (b * (1 - a - b) - (1 - a - b) * a), 
            sq_nonneg (a * b - (1 - a - b) * a), sq_nonneg (a - b), sq_nonneg (a - (1 - a - b)), sq_nonneg (b - (1 - a - b))
            ]
      linarith
    linarith
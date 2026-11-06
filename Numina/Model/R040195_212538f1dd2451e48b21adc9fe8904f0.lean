import Mathlib

open BigOperators Real Set

theorem inequalities_33663 {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ)
  (hf : f = λ x => (a - x)^6 - 3 * a * (a - x)^5 + (5 / 2) * a^2 * (a - x)^4 - (1 / 2) * a^4 * (a - x)^2) :
  ∀ x ∈ Ioo 0 a, f x < 0 := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have h1 : 0 < x := by linarith
  have h2 : x < a := by linarith
  have h3 : 0 < a - x := by linarith
  have h4 : (a - x) ^ 2 > 0 := by positivity
  have h5 : x ^ 2 > 0 := by positivity
  have h6 : (a - x) ^ 2 * x ^ 2 > 0 := mul_pos h4 h5
  have h7 : f x = (a - x) ^ 2 * x ^ 2 * ((a - x) ^ 2 - a * (a - x) - a ^ 2 / 2) := by
    rw [hf]
    ring_nf
  rw [h7]
  have h8 : (a - x) ^ 2 - a * (a - x) - a ^ 2 / 2 < 0 := by
    have h9 : 0 < (a - x) := by linarith
    have h10 : (a - x) < a := by linarith
    nlinarith [sq_nonneg ((a - x) - a / 2), sq_pos_of_pos (show 0 < a by linarith), sq_nonneg ((a - x) - (a * (1 + Real.sqrt 3) / 2)), Real.sqrt_pos.mpr (by nlinarith : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by nlinarith), mul_pos (show 0 < a by linarith) (show 0 < a by linarith)]
  apply mul_neg_of_pos_of_neg
  · positivity
  · linarith
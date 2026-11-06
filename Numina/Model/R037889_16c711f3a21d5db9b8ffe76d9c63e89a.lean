import Mathlib

open Real

namespace Inequalities_605320

theorem Inequalities_605320 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcond : a * b * c * (a + b + c) = 3) :
    (a + b) * (b + c) * (c + a) ≥ 8 ∧ ((a = 1 ∧ b = 1 ∧ c = 1) → (a + b) * (b + c) * (c + a) = 8):= by
  constructor
  · -- First part: prove the inequality
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (show 0 < a * b by positivity) (show 0 < c by linarith)]
  · -- Second part: prove when the equality holds
    intro h_eq
    rcases h_eq with ⟨ha1, hb1, hc1⟩
    rw [ha1, hb1, hc1]
    norm_num
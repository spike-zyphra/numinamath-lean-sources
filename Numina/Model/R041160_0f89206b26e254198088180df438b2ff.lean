import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_308611 (k : ℝ) :
  (∀ a b c d : ℝ, a ∈ Icc 0 1 → b ∈ Icc 0 1 → c ∈ Icc 0 1 → d ∈ Icc 0 1 →
    a^2 * b + b^2 * c + c^2 * d + d^2 * a + 4 ≥
    k * (a^2 + b^2 + c^2 + d^2)) ↔ k ≤ 2 := by
  constructor
  · -- Assume the inequality holds for all a, b, c, d in [0, 1], prove k ≤ 2.
    intro h
    have h1 := h 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h1 -- simplifies the inequality with a,b,c,d = 1
    linarith -- solves `6 ≥ k * 4` for k.
  · -- Assume k ≤ 2.
    intro hk a b c d ha hb hc hd
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rcases hc with ⟨hc0, hc1⟩
    rcases hd with ⟨hd0, hd1⟩
    have h1 : a^2 * b + b^2 * c + c^2 * d + d^2 * a + 4 ≥ 2 * (a^2 + b^2 + c^2 + d^2) := by
      nlinarith [mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ 1 - a by linarith),
        mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ 1 - b by linarith),
        mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ 1 - c by linarith),
        mul_nonneg (show 0 ≤ d by linarith) (show 0 ≤ 1 - d by linarith),
        mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
        mul_nonneg (show 0 ≤ b by linarith) (show 0 ≤ c by linarith),
        mul_nonneg (show 0 ≤ c by linarith) (show 0 ≤ d by linarith),
        mul_nonneg (show 0 ≤ d by linarith) (show 0 ≤ a by linarith)]
    have h2 : k * (a^2 + b^2 + c^2 + d^2) ≤ 2 * (a^2 + b^2 + c^2 + d^2) := by
      have h3 : k ≤ 2 := hk
      have h4 : (a^2 + b^2 + c^2 + d^2 : ℝ) ≥ 0 := by
        positivity
      nlinarith
    linarith [h1, h2]
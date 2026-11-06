import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_165830 :
  IsGreatest {k : ℝ | ∀ a b c d : ℝ, a ∈ Icc 0 1 → b ∈ Icc 0 1 → c ∈ Icc 0 1 → d ∈ Icc 0 1 →
    a^2 * b + b^2 * c + c^2 * d + d^2 * a + 4 ≥ k * (a^2 + b^2 + c^2 + d^2)} 2 := by
  constructor
  · -- First part: Show that 2 is in the set
    intro a b c d ha hb hc hd
    rcases ha with ⟨ha0, ha1⟩
    rcases hb with ⟨hb0, hb1⟩
    rcases hc with ⟨hc0, hc1⟩
    rcases hd with ⟨hd0, hd1⟩
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), sq_nonneg (d - 1),
      sq_nonneg (a^2 - 1), sq_nonneg (b^2 - 1), sq_nonneg (c^2 - 1), sq_nonneg (d^2 - 1),
      mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - a by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ 1 - b by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ c by linarith) (show (0 : ℝ) ≤ 1 - c by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ d by linarith) (show (0 : ℝ) ≤ 1 - d by linarith)
    ]
  
  · -- Second part: Show that 2 is the greatest element in the set
    intro k hk
    have h4 : ∀ a b c d : ℝ, a ∈ Icc 0 1 → b ∈ Icc 0 1 → c ∈ Icc 0 1 → d ∈ Icc 0 1 → a^2 * b + b^2 * c + c^2 * d + d^2 * a + 4 ≥ k * (a^2 + b^2 + c^2 + d^2) := by
      simpa using hk
    have h5 := h4 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    norm_num at h5
    nlinarith
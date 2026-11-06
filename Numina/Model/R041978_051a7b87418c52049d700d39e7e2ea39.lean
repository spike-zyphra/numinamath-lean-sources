import Mathlib

theorem inequalities_66490 (n : ℕ) :
    (∀ a b c : ℕ, a > 0 → b > 0 → c > 0 → (a + b + c)^3 ≤ n * (a^3 + b^3 + c^3)) ↔
    n ≥ 9 := by
  constructor
  · -- First, we show that if the inequality holds for all a, b, c, then n ≥ 9.
    intro h
    have h111 := h 1 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h111
    by_contra h2
    push_neg at h2
    have : n < 9 := by omega
    have h3 : n ≤ 8 := by omega
    interval_cases n <;> omega
  · -- Now, we prove the reverse direction. If n ≥ 9, then the inequality holds for all a, b, c.
    intro hn a b c ha hb hc
    have h9 : (a + b + c) ^ 3 ≤ 9 * (a ^ 3 + b ^ 3 + c ^ 3) := by
      nlinarith [sq_nonneg (a - b : ℤ), sq_nonneg (a - c : ℤ), sq_nonneg (b - c : ℤ), 
          sq_nonneg (a + b - c : ℤ), sq_nonneg (a + c - b : ℤ), sq_nonneg (b + c - a : ℤ), 
          mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
          mul_pos (show 0 < a by linarith) (show 0 < c by linarith), 
          mul_pos (show 0 < b by linarith) (show 0 < c by linarith)
        ]
    have h1 : n * (a ^ 3 + b ^ 3 + c ^ 3) ≥ 9 * (a ^ 3 + b ^ 3 + c ^ 3) := by
      have h2 : n ≥ 9 := by linarith
      have h3 : a ^ 3 + b ^ 3 + c ^ 3 ≥ 0 := by positivity
      nlinarith
    linarith [h9, h1]
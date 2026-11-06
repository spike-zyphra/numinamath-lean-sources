import Mathlib

open Real
open scoped BigOperators

theorem inequalities_602521 {n : ℕ} (hn : n > 2) (a b c : ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : a^2 + b^2 = c^2) :
  a^n + b^n < c^n := by

  have h1 : n ≥ 3 := by linarith

  have h2 : a < c := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - a), sq_nonneg (c - b), h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h3 : b < c := by 
    nlinarith [sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (c - b), h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h4 : ∀ k : ℕ, a ^ (k + 3) + b ^ (k + 3) < c ^ (k + 3) := by 
    intro k
    induction k with 
    | zero =>
      have h5 : a ^ 3 + b ^ 3 < c ^ 3 := by 
        nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), pow_pos ha 3, pow_pos hb 3, pow_pos hc 3, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h]
      simpa using h5 
    | succ k ih =>
      have h5 : a ^ (k + 4) + b ^ (k + 4) < c ^ (k + 4) := by 
        have h6 : a ^ (k + 4) + b ^ (k + 4) = (a ^ (k + 3)) * a + (b ^ (k + 3)) * b := by 
          ring_nf 
        rw [h6]
        have h7 : (a ^ (k + 3)) * a + (b ^ (k + 3)) * b < c ^ (k + 3) * (c) := by
          have h9 : a < c := h2 
          have h10 : b < c := h3
          have h11 : a ^ (k + 3) < c ^ (k + 3) := by
            apply pow_lt_pow_left 
            all_goals linarith 
          have h12 : b ^ (k + 3) < c ^ (k + 3) := by 
            apply pow_lt_pow_left 
            all_goals linarith 
          nlinarith [pow_pos ha (k + 3), pow_pos hb (k + 3), pow_pos hc (k + 3), h, pow_pos (show 0 < a * b by nlinarith) (k + 2), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
        have h8 : c ^ (k + 4) = c ^ (k + 3) * c := by 
          ring_nf 
        rw [h8] 
        linarith 
      simpa using h5 
  have h5 : ∃ k : ℕ, n = k + 3 := by 
    refine' ⟨n - 3, by omega⟩ 
  rcases h5 with ⟨k, hk⟩ 
  rw [hk] 
  exact h4 k
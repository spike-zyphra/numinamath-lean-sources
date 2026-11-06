import Mathlib

open Real
open scoped BigOperators

theorem inequalities_233679 {n : ℕ} (hn : n ≥ 2) (x : ℝ) (hx : |x| < 1) :
    2^n > (1 - x)^n + (1 + x)^n := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : 0 < 1 - x := by nlinarith
  have h4 : 0 < 1 + x := by nlinarith

  have h5 : ∀ (n : ℕ), n ≥ 2 → 2 ^ n > (1 - x) ^ n + (1 + x) ^ n := by
    intro n hn
    have h7 : n ≥ 2 := hn
    have baseCase : 2 ^ 2 > (1 - x) ^ 2 + (1 + x) ^ 2 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 2), 
                  hx, h1, h2, 
                  mul_pos (show 0 < (1 - x) by linarith) (show 0 < 1 + x by linarith)
                ]
    have stepCase : ∀ k, k ≥ 2 → 2 ^ k > (1 - x) ^ k + (1 + x) ^ k → 2 ^ (k + 1) > (1 - x) ^ (k + 1) + (1 + x) ^ (k + 1) := by
      intro k hk hk1
      have eq1 : (1 - x) ^ (k + 1) + (1 + x) ^ (k + 1) = (1 - x) * ( (1 - x )^k ) + (1 + x) * ( (1 + x )^k ) := by
        ring
      rw [eq1] at *
      have fact1 : 0 < 1 - x := h3
      have fact2 : 0 < 1 + x := h4

      by_cases h8 : x ≥ 0 
      · -- x ≥ 0 
        have h10 : (1 + x) ^ k ≥ (1 - x) ^ k := by
          have h11 : (1 + x) ≥ (1 - x) := by nlinarith
          have h12 : (1 + x) ^ k ≥ (1 - x) ^ k := by
            apply pow_le_pow_left 
            all_goals nlinarith
          linarith 
        have h13 : (1 - x) * ( (1 - x )^k ) + (1 + x) * ( (1 + x )^k ) < (2 : ℝ) * (2 ^ k ) := by
          nlinarith [h10, sq_nonneg ( (1 - x ) ^ k - (1 + x ) ^ k ), 
            sq_nonneg (x), 
            pow_pos (show 0 < 1 - x by linarith) k, 
            pow_pos (show 0 < 1 + x by linarith) k 
          ]
        have h14 : (2 : ℝ) ^ (k + 1 ) = (2 : ℝ) * (2 ^ k ) := by
          ring_nf
        have h15 : (1 - x) * ( (1 - x )^k ) + (1 + x) * ( (1 + x )^k ) < (2 : ℝ) ^ (k + 1 ) := by
          nlinarith [h13, h14 ]
        linarith [h15, eq1]
      · -- x < 0 
        have h16 : x < 0 := by linarith 
        have h17 : (1 - x) ^ k ≥ (1 + x) ^ k := by 
          have h18 : (1 - x) ≥ (1 + x) := by nlinarith
          have h19 : (1 - x) ^ k ≥ (1 + x) ^ k := by 
            apply pow_le_pow_left 
            all_goals nlinarith
          linarith 
        have h18 : (1 - x) * ( (1 - x )^k ) + (1 + x) * ( (1 + x )^k ) < (2 : ℝ) * (2 ^ k ) := by 
          nlinarith [h17, sq_nonneg ( (1 - x )^k - (1 + x )^k ), 
            sq_nonneg (x), 
            pow_pos (show 0 < 1 - x by linarith) k, 
            pow_pos (show 0 < 1 + x by linarith) k 
          ]
        have h19 : (2 : ℝ) ^ (k + 1 ) = (2 : ℝ) * (2 ^ k ) := by 
          ring_nf 
        have h20 : (1 - x) * ( (1 - x )^k ) + (1 + x) * ( (1 + x )^k ) < (2 : ℝ) ^ (k + 1 ) := by 
          nlinarith [h18, h19 ]
        linarith [h20, eq1]
    exact Nat.le_induction baseCase stepCase n h7 
  specialize h5 n hn 
  simpa using h5
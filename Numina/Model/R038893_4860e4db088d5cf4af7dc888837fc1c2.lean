import Mathlib

open Nat

theorem algebra_129196 (x : ℕ) (hx : x > 0) : x ! = (x:ℤ) ^ 3 - 11 * x + 4 ↔ x = 4 := by
  constructor
  · -- Assume x! = x^3 - 11 x + 4, prove x = 4
    intro h
    have eq1 : (x : ℤ) > 0 := by exact_mod_cast hx
    by_cases h1 : x < 5
    · -- If x < 5
      interval_cases x <;> try { 
        contradiction
      }
      all_goals
      omega
    · -- x ≥ 5
      have h2 : x ≥ 5 := by 
        by_contra h'
        push_neg at h'
        have h3 : x < 5 := by omega
        linarith
      have h3 : (x : ℤ) ≥ 5 := by exact_mod_cast h2
      have h4 : (x ! : ℤ) > (x:ℤ) ^ 3 - 11 * x + 4 := by
        have h5 : ∀ n : ℕ, n ≥ 5 → (n ! : ℤ) > (n : ℤ) ^ 3 - 11 * (n : ℤ) + 4 := by
          intro n hn
          have base5 : (5 ! : ℤ) > (5 : ℤ) ^ 3 - 11 * (5 : ℤ) + 4 := by 
            norm_num [Nat.factorial]
          have step : ∀ (k : ℕ), k ≥ 5 → (k ! : ℤ) > (k : ℤ) ^ 3 - 11 * (k : ℤ) + 4 → ( (k + 1) ! : ℤ) > ((k + 1) : ℤ) ^ 3 - 11 * ((k + 1) : ℤ) + 4 := by
            intro k hk h
            have eq2 : ((k + 1) ! : ℤ) = ( (k + 1) : ℤ) * ((k !) : ℤ) := by
              simp [Nat.factorial]
              <;> ring
            rw [eq2]
            nlinarith [ sq_nonneg (( (k : ℤ) - 2 ) : ℤ), sq_nonneg (( (k : ℤ) - 1 ) : ℤ), sq_nonneg (( (k : ℤ) : ℤ) ), sq_nonneg (( (k: ℤ) + 1 ) : ℤ), sq_nonneg (( (k: ℤ) + 2 ) : ℤ), sq_pos_of_pos (show 0 < (k: ℤ) by omega ), sq_pos_of_pos (show (0:ℤ) < k + 1 by omega), h, mul_pos (show (0:ℤ) < k + 1 by omega) (show 0 < (k: ℤ) by omega ) ]
          exact Nat.le_induction base5 step n hn
        specialize h5 x h2
        simpa using h5
      linarith [h, h4]
  · -- Assume x = 4, prove x! = x^3 - 11 * x + 4
    intro h
    rw [h]
    all_goals
    native_decide
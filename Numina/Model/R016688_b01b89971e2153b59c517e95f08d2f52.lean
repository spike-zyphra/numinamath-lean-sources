import Mathlib

open Real

theorem inequalities_278895 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 < n) :
    (1 + x) ^ n > 1 + n * x := by
  have base2 : (1 + x) ^ 2 > 1 + (2 : ℕ) * x := by 
    norm_num
    have h1 : x ^ 2 > 0 := by
      exact sq_pos_of_pos hx
    nlinarith
  have step : ∀ k : ℕ, k ≥ 2 → (1 + x) ^ k > 1 + (k : ℕ) * x → (1 + x) ^ (k + 1) > 1 + ((k + 1 : ℕ)) * x := by
    intro k hk ih
    have h1 : (1 + x) ^ (k + 1) = ( (1 + x) ^ k ) * (1 + x) := by ring
    have eq : (1 + x) ^ k > 1 + (k : ℕ) * x := ih
    have h2 : (1 + x) ^ (k + 1) > (1 + (k : ℕ) * x) * (1 + x) := by
      nlinarith [h1, eq, show 0 < 1 + x by linarith, sq_nonneg x]
    have h3 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
    nlinarith [h2, h3, sq_nonneg x, show (k : ℝ) ≥ (2 : ℝ) by exact_mod_cast (show k ≥ 2 by omega)]
  have h3 : ∀ m : ℕ, m ≥ 2 → (1 + x) ^ m > 1 + (m : ℕ) * x := by
    intro m hm
    exact Nat.le_induction base2 step m hm
  have h4 : n ≥ 2 := by omega
  specialize h3 n h4
  simpa using h3
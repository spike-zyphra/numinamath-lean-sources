import Mathlib


open Nat



theorem number_theory_65127 (k : ℕ) (hk : Even k ∧ k > 0)
    (x : ℕ → ℕ) (hx1 : x 1 = 1) (hxn : ∀ n, x (n + 1) = k ^ x n + 1) :
    ∀ n ≥ 2, (x n) ^ 2 ∣ x (n - 1) * x (n + 1) := by
  have eq2 : x 1 = k ^ x 0 + 1 := hxn 0
  rw [hx1] at eq2
  have h5 : k ^ x 0 = 0 := by
    omega
  have h8 : k ≥ 1 := by linarith [hk.right]
  have h10 : k ^ x 0 ≥ 1 := by
    have h1 : k ≥ 1 := h8 
    have h2 : k ^ x 0 ≥ 1 := by
      apply Nat.one_le_pow 
      all_goals linarith
    linarith
  linarith
import Mathlib

theorem algebra_50602 (n : ℕ) (hn : n > 0) :
    ¬(n^2 + 8 * n + 15) % (n + 4) = 0 := by
  by_contra h
  have h1 : (n + 4) ∣ (n^2 + 8 * n + 15) := by 
    exact Nat.dvd_of_mod_eq_zero h
  rcases h1 with ⟨k, hk⟩
  have h3 : n^2 + 8 * n + 15 = (n + 4) * k := by 
    linarith
  have h4 : k > n + 3 := by
    nlinarith [sq_nonneg (k - (n + 3) : ℤ), sq_nonneg ((n : ℤ)), sq_nonneg ((k : ℤ)), sq_nonneg ((n + 4 : ℤ))]
  have h5 : k ≥ n + 4 := by omega
  have h6 : (n + 4) * k ≥ (n + 4) * (n + 4) := by 
    nlinarith [h5, sq_nonneg (n + 4)]
  have h7 : (n ^ 2 + 8 * n + 15) ≥ (n + 4) * (n + 4) := by
    nlinarith [h3, h6]
  nlinarith [sq_nonneg (n + 4), sq_nonneg (k), sq_nonneg (n)]
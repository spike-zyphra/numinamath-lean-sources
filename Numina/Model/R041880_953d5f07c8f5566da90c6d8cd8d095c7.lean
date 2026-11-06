import Mathlib

theorem number_theory_188680 (n : ℕ) (h : Odd n) : 11 ∣ 10^n + 1 := by
  rcases h with ⟨k, hk⟩
  have h1 : ∀ (k : ℕ), 11 ∣ 10 ^ (2 * k + 1) + 1 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      have h2 : 10 ^ (2 * (k + 1) + 1) + 1 = 100 * (10 ^ (2 * k + 1)) + 1 := by
        ring_nf
      rw [h2]
      omega
  have eq1 : n = 2 * k + 1 := by 
    omega
  rw [eq1]
  apply h1 k
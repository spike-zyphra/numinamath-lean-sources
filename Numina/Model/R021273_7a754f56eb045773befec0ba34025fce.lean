import Mathlib

theorem number_theory_226608 (F : ℕ → ℕ) (hF : ∀ n, F n = F (n - 1) + F (n - 2)) (hF0 : F 0 = 0) (hF1 : F 1 = 1) :
    (∀ n ≥ 2, F (n + 5) > 10 * F n) ∧ (∀ n k, F (n + 1) < 10 ^ k → n ≤ 5 * k) := by
  have h1 := hF 1
  have h2 : F 1 = F 0 + F 0 := by 
    norm_num [Nat.sub_eq_zero_of_le] at h1 ⊢
    all_goals
      omega
  rw [hF0] at h2
  omega
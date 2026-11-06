import Mathlib

theorem number_theory_127001 (p : ℕ) (hp : Nat.Prime p) (hne2 : p ≠ 2) (hne3 : p ≠ 3) :
    p^2 ≡ 1 [MOD 12] := by 
  have h1 : p ≥ 4 := by 
    by_contra h
    push_neg at h
    interval_cases p <;> norm_num at hp hne2 hne3
  have h2 : p % 2 = 1 := by
    by_contra h
    push_neg at h
    have : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals
        omega
    tauto
  have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
    by_contra h
    push_neg at h
    have : p % 3 = 0 := by
      omega
    have : ¬ Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 3 ∣ p by omega)
      all_goals
        omega
    tauto
  have h4 : p % 12 = 1 ∨ p % 12 = 5 ∨ p % 12 = 7 ∨ p % 12 = 11 := by
    omega 
  rcases h4 with (h | h | h | h)
  · -- Case p % 12 = 1
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 12 = 5
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 12 = 7
    simp [Nat.ModEq, Nat.pow_mod, h]
  · -- Case p % 12 = 11
    simp [Nat.ModEq, Nat.pow_mod, h]
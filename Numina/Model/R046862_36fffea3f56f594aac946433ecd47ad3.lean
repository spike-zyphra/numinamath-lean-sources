import Mathlib

theorem number_theory_124290 (x : ℕ) (hx : x.Prime) (h : ∃ y z w v u : ℕ, y.Prime ∧ z.Prime ∧ w.Prime ∧ v.Prime ∧ u.Prime ∧ x + 2 = y ∧ x + 6 = z ∧ x + 8 = w ∧ x + 12 = v ∧ x + 14 = u) :
    x = 5 := by
  rcases h with ⟨y, z, w, v, u, hy, hz, hw, hv, hu, h1, h2, h3, h4, h5⟩
  have h6 : y = x + 2 := by omega
  have h7 : z = x + 6 := by omega
  have h8 : w = x + 8 := by omega
  have h9 : v = x + 12 := by omega
  have h10 : u = x + 14 := by omega
  rw [h6] at hy
  rw [h7] at hz
  rw [h8] at hw
  rw [h9] at hv
  rw [h10] at hu
  by_cases h5' : x ≤ 23
  · -- Case where x ≤ 23
    interval_cases x <;> norm_num at hx hy hz hw hv hu <;> try { all_goals tauto }
  · -- Case where x > 23
    push_neg at h5'
    have h5 : x % 5 = 0 ∨ x % 5 = 1 ∨ x % 5 = 2 ∨ x % 5 = 3 ∨ x % 5 = 4 := by omega
    rcases h5 with (h5 | h5 | h5 | h5 | h5)
    · -- Case where x % 5 = 0
      have h11 : x % 5 = 0 := h5
      have h5div : ¬x.Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x by omega) (by omega) (by omega)
      exfalso
      tauto
    · -- Case where x % 5 = 1
      have h11 : u % 5 = 0 := by
        omega
      have h13 : ¬ (x + 14).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x + 14 by omega)
        all_goals
          omega
      have h14 : (x + 14).Prime := by 
        simpa using hu
      exfalso
      tauto
    · -- Case where x % 5 = 2
      have h11 : w % 5 = 0 := by
        omega
      have h13 : ¬ (x + 8).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x + 8 by omega)
        all_goals
          omega
      have h14 : (x + 8).Prime := by 
        simpa using hw
      exfalso
      tauto
    · -- Case where x % 5 = 3
      have h11 : y % 5 = 0 := by
        omega
      have h13 : ¬ (x + 2).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x + 2 by omega)
        all_goals
          omega
      have h14 : (x + 2).Prime := by 
        simpa using hy
      exfalso
      tauto
    · -- Case where x % 5 = 4
      have h11 : z % 5 = 0 := by
        omega
      have h13 : ¬ (x + 6).Prime := by
        apply Nat.not_prime_of_dvd_of_lt (show 5 ∣ x + 6 by omega)
        all_goals
          omega
      have h14 : (x + 6).Prime := by 
        simpa using hz
      exfalso
      tauto
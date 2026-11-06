import Mathlib


theorem number_theory_90542 (p : ℕ) (hp : Nat.Prime p) (h : 3 < p) :
    ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ ∃ i : ℕ, i ∈ Finset.Icc 3 (p - 2) ∧
      (i / p ^ 2 : ℚ) = 1 / x + 1 / y := by

  have h2 : p ≥ 4 := by omega
  have h3 : p ≥ 5 := by
    by_contra h4
    push_neg at h4
    interval_cases p <;> norm_num at hp h

  have h4 : p % 2 = 1 := by
    by_contra h4
    have h5 : p % 2 = 0 := by omega
    have h7 : p > 2 := by omega
    have h8 : ¬Nat.Prime p := by
      apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
      all_goals omega
    contradiction

  have h5 : (p + 1) % 2 = 0 := by
    omega

  have h30 : ∃ k : ℕ, (p + 1) = 2 * k := by
    refine' ⟨(p + 1) / 2, by omega⟩

  rcases h30 with ⟨k, hk⟩

  have hk10 : 3 ≤ k := by
    have h30 : p ≥ 5 := h3
    omega

  have hk11 : k ≤ p - 2 := by
    have h30 : p ≥ 5 := h3
    omega

  use 2 * p, 2 * p ^ 2
  constructor
  ·
    nlinarith
  constructor
  ·
    nlinarith
  use k
  constructor
  ·
    have hk0 : k ≥ 3 := hk10
    have hk1 : k ≤ p - 2 := hk11
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  ·
    have hk2 : (k : ℚ) = (p + 1) / 2 := by
      have hk00 : 2 * k = p + 1 := by
        omega
      have hk11 : (2 * k : ℚ) = (p + 1 : ℚ) := by
        exact_mod_cast (show (2 * k : ℚ) = (p + 1 : ℚ) by exact_mod_cast hk00)
      field_simp at *
      linarith
    have eq1 : ((k : ℚ) / p ^ 2 : ℚ) = (1 / (2 * p) + 1 / (2 * p ^ 2) : ℚ) := by
      rw [show (k : ℚ) = (p + 1) / 2 by linarith [hk2]]
      field_simp
      ring
    simpa using eq1
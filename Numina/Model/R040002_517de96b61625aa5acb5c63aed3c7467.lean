import Mathlib

theorem number_theory_139692 (k : ℕ) :
    ∀ N, ∃ n : ℕ, n > N ∧ ∀ i ∈ Finset.Icc 1 k, ¬Nat.Prime (n + i) := by
  intro N
  use (N + 1) * (k + 1).factorial + 1
  constructor
  · -- Show n > N
    have hk1 : (N + 1) * (k + 1).factorial + 1 > N := by
      have hk2 : (N + 1) * (k + 1).factorial ≥ (N + 1) := by
        have hk3 : (k + 1).factorial ≥ 1 := by
          apply Nat.factorial_pos
        nlinarith
      omega
    linarith
  · -- Show that for all i in Icc 1 k, ¬Nat.Prime (n + i)
    intro i hi
    have h1 : i ∈ Finset.Icc 1 k := hi
    rw [Finset.mem_Icc] at h1
    rcases h1 with ⟨h1, h12⟩
    have hk4 : i + 1 ≤ k + 1 := by omega
    have hk5 : i + 1 ∣ (N + 1) * (k + 1).factorial := by
      have hk6 : i + 1 ∣ (k + 1).factorial := by
        apply Nat.dvd_factorial
        · omega
        · omega
      have hk7 : i + 1 ∣ (N + 1) * (k + 1).factorial := by
        have hk8 : i + 1 ∣ (k + 1).factorial := hk6
        have hk9 : (k + 1).factorial ∣ (N + 1) * (k + 1).factorial := by
          use (N + 1)
          all_goals nlinarith
        exact dvd_trans hk8 hk9
      exact hk7
    have hk10 : i + 1 ∣ (N + 1) * (k + 1).factorial + (i + 1) := by
      have hk11 : i + 1 ∣ (N + 1) * (k + 1).factorial := hk5
      have hk12 : i + 1 ∣ (i + 1) := by
        exact dvd_refl (i + 1)
      exact Nat.dvd_add hk11 hk12
    have hk14 : i + 1 ∣ (N + 1) * (k + 1).factorial + 1 + i := by
      have hk13 : (N + 1) * (k + 1).factorial + 1 + i = (N + 1) * (k + 1).factorial + (i + 1) := by omega
      rw [hk13] at *
      exact hk10
    -- Show that number is not prime
    have hk15 : ¬Nat.Prime ((N + 1) * (k + 1).factorial + 1 + i) := by
      have hk16 : i + 1 ∣ (N + 1) * (k + 1).factorial + 1 + i := hk14
      have hk17 : i + 1 > 1 := by
        omega
      have hk18 : i + 1 < (N + 1) * (k + 1).factorial + 1 + i := by
        have hk19 : (N + 1) * (k + 1).factorial > 0 := by
          have hk20 : (k + 1).factorial ≥ 1 := by
            apply Nat.factorial_pos
          nlinarith [show N + 1 ≥ 1 by omega]
        nlinarith
      apply Nat.not_prime_of_dvd_of_lt hk16 (by omega) (by omega)
    simpa using hk15
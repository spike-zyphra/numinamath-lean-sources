import Mathlib

theorem number_theory_4220 : IsGreatest {n | ∃ A : ℕ, 0 < A ∧ ∏ i ∈ Finset.Icc 1 2019, i = 48^n * A} 502 := by 
  constructor
  · -- Show that 502 is achievable
    use Nat.factorial 2019 / 48 ^ 502
    constructor
    · -- Show that A > 0
      native_decide
    · -- Show that the equation holds
      native_decide
  · -- Show that 502 is the greatest
    intro n hn
    rcases hn with ⟨A, hA1, hA2⟩
    by_contra h
    push_neg at h
    have hn1 : n ≥ 503 := by omega
    have h1 : 48 ^ 503 ∣ ∏ i ∈ Finset.Icc 1 2019, i := by 
      rw [hA2]
      have h9 : 48 ^ 503 ∣ 48 ^ n * A := by 
        have h10 : 503 ≤ n := by 
          omega 
        have h11 : 48 ^ 503 ∣ 48 ^ n := by 
          apply pow_dvd_pow 
          all_goals 
            omega 
        have h12 : 48 ^ 503 ∣ 48 ^ n * A := by 
          apply dvd_mul_of_dvd_left 
          exact h11 
        exact h12 
      exact h9 
    have h2 : ¬ (48 ^ 503 ∣ ∏ i ∈ Finset.Icc 1 2019, i) := by
      native_decide
    omega
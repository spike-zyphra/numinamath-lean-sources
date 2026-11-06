import Mathlib

theorem number_theory_258506 {A B C : ℕ} (hA : A.gcd B = 2) (hB : A.lcm B = 60)
    (hC : A.gcd C = 3) (hD : A.lcm C = 42) :
    A = 6 ∧ B = 20 ∧ C = 21 := by
  have h1 : A * B = 120 := by
    calc
      A * B = Nat.gcd A B * Nat.lcm A B := by rw [Nat.gcd_mul_lcm]
      _ = 2 * 60 := by rw [hA, hB]
      _ = 120 := by norm_num

  have h2 : A * C = 126 := by
    calc
      A * C = Nat.gcd A C * Nat.lcm A C := by rw [Nat.gcd_mul_lcm]
      _ = 3 * 42 := by rw [hC, hD]
      _ = 126 := by norm_num

  have h3 : A ∣ 120 := by
    use B
    all_goals
      nlinarith [h1]

  have h4 : A ∣ 126 := by
    use C
    all_goals
      nlinarith [h2]

  have h5 : A ∣ 6 := by
    exact Nat.dvd_gcd h3 h4

  have h6 : A = 1 ∨ A = 2 ∨ A = 3 ∨ A = 6 := by
    have h55 : A ∣ 6 := h5
    have h77 : A ≤ 6 := by
      exact Nat.le_of_dvd (by norm_num) h55
    interval_cases A <;> tauto

  rcases h6 with (r | r | r | r)
  · -- A = 1
    rw [show A = 1 by omega] at h1 hA
    have h20 : B = 120 := by
      nlinarith
    rw [h20] at hA
    norm_num [Nat.gcd] at hA
  · -- A = 2
    rw [show A = 2 by omega] at h1 h2 hA hC
    have h20 : B = 60 := by
      nlinarith
    have h30 : C = 63 := by
      nlinarith
    rw [h30] at hC
    norm_num [Nat.gcd] at hC
  · -- A = 3
    rw [show A = 3 by omega] at h1 hA h2 hC
    have h20 : B = 40 := by
      nlinarith
    rw [h20] at hA
    norm_num [Nat.gcd] at hA
  · -- A = 6
    have h12 : A = 6 := by omega
    have h120 : B = 20 := by
      rw [show A = 6 by omega] at h1
      nlinarith
    have h121 : C = 21 := by
      rw [show A = 6 by omega] at h2
      nlinarith
    constructor
    · exact h12
    constructor
    · exact h120
    · exact h121
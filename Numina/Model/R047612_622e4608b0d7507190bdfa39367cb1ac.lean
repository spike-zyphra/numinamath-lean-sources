import Mathlib

theorem algebra_134809 :
    IsGreatest {b : ℤ | ∃ x : ℤ, x^2 + b * x - 9600 = 0 ∧ 10 ∣ x ∧ 12 ∣ x} 9599 := by
  constructor
  · -- First show that 9599 is in the set
    use -9600
    norm_num
  · -- Now show that 9599 is greatest
    intro b hb
    rcases hb with ⟨x, h1, h2, h3⟩
    have h5 : 60 ∣ x := by
      have h5 : 10 ∣ x := by
        exact h2
      have h6 : 12 ∣ x := by
        exact h3
      omega
    rcases h5 with ⟨k, hk⟩
    rw [hk] at h1
    have h6 : 3600 * k ^ 2 + 60 * b * k - 9600 = 0 := by
      nlinarith
    have h7 : 60 * k ^ 2 + b * k - 160 = 0 := by
      linarith
    by_cases hk0 : k = 0
    · -- k = 0
      rw [hk0] at h7
      nlinarith
    · -- k ≠ 0
      have h4 : k ≠ 0 := by
        intro h
        apply hk0
        omega
      -- Now, solve for b from h7
      have h8 : b * k = 160 - 60 * k ^ 2 := by linarith
      -- Show k divides 160
      have h4 : k ∣ 160 := by
        use (b + 60 * k)
        nlinarith
      have h11 : k ≤ 160 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h12 : k ≥ -160 := by
        have : -k ∣ 160 := by
          exact Int.neg_dvd.2 h4
        have h13 : -k ≤ 160 := by
          apply Int.le_of_dvd (by norm_num) this
        linarith
      interval_cases k <;> omega
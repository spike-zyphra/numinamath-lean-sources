import Mathlib

/-A number N has three digits when expressed in base 7.
When N is expressed in base 9 the digits are reversed.
Then the middle digit is:-/

theorem number_theory_95708 {N: ℤ} (a b c: ℤ) (lb: 0 ≤ b) (rb: b ≤ 6)  
  (h1: N = 49 * a + 7 * b + c) (h2: N = 81 * c + 9 * b + a): b = 0 := by

  rw [h2] at h1
  replace h1: 2 * b = 48 * a - 80 * c := by
    nlinarith
  replace h1: b = 24 * a - 40 * c := by
    nlinarith
  replace h1: b = 8 * (3 * a - 5 * c) := by
    nlinarith
  
  -- hence 8 ∣ b
  have d: 8 ∣ b := by
    rw [h1]
    simp
  apply exists_eq_mul_right_of_dvd at d
  obtain ⟨k, hk⟩ := d
  have lk: k < 1 := by omega
  replace lk: k = 0 := by omega
  simp [lk] at hk
  exact hk
  
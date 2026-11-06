import Mathlib

theorem number_theory_285174 (a b c d l k : ℤ) (h : k ≠ 0) :
    (a * l + b) % k = 0 ∧ (c * l + d) % k = 0 → (a * d - b * c) % k = 0 := by
  intro h1
  have h1' : (a * l + b) % k = 0 := h1.1
  have h2' : (c * l + d) % k = 0 := h1.2

  have h11 : k ∣ (a * l + b) := by
    exact Int.dvd_of_emod_eq_zero h1'
  have h22 : k ∣ (c * l + d) := by
    exact Int.dvd_of_emod_eq_zero h2'

  have h3 : k ∣ (a * d - b * c) := by
    have eq : a * d - b * c = (-c) * (a * l + b) + a * (c * l + d) := by
      ring

    have h31 : k ∣ (-c) * (a * l + b) := by 
      have h11' : k ∣ a * l + b := h11
      apply dvd_mul_of_dvd_right 
      exact h11'

    have h32 : k ∣ a * (c * l + d) := by
      have h22' : k ∣ c * l + d := h22
      apply dvd_mul_of_dvd_right 
      exact h22'

    have h33 : k ∣ ((-c) * (a * l + b) + a * (c * l + d)) := by
      apply Dvd.dvd.add
      · exact h31
      · exact h32

    have : k ∣ a * d - b * c := by
      rw [eq] at *
      exact h33
    exact this

  have h4 : (a * d - b * c) % k = 0 := by 
    exact Int.emod_eq_zero_of_dvd h3
  exact h4
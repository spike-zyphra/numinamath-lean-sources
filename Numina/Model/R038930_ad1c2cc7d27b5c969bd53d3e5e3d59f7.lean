import Mathlib

theorem number_theory_101312 {a b c d n : ℕ} (h1 : 2017 ∣ a * n + b) (h2 : 2017 ∣ c * n + d) :
  2017 ∣ a * d - b * c
:= by

  have h5 : a * (c * n + d) - c * (a * n + b) = a * d - b * c := by
    ring_nf
    <;> omega

  have h6 : 2017 ∣ a * (c * n + d) := by
    have h5' : 2017 ∣ c * n + d := h2
    have h7 : 2017 ∣ a * (c * n + d) := by
      apply dvd_mul_of_dvd_right
      exact h5'
    exact h7

  have h7 : 2017 ∣ c * (a * n + b) := by
    have h5' : 2017 ∣ a * n + b := h1
    have h8 : 2017 ∣ c * (a * n + b) := by
      apply dvd_mul_of_dvd_right
      exact h5'
    exact h8

  have h6' : 2017 ∣ (a * (c * n + d) - c * (a * n + b)) := by
    apply Nat.dvd_sub'
    · exact h6
    · exact h7

  have h8 : a * (c * n + d) - c * (a * n + b) = a * d - b * c := h5
  rw [h8] at h6'
  exact h6'
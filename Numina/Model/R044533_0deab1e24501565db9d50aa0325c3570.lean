import Mathlib

theorem number_theory_36863 (n : ℤ) (hn : n > 0) (a b c d : ℤ)
    (h1 : n ∣ a + b + c + d) (h2 : n ∣ a^2 + b^2 + c^2 + d^2) :
    n ∣ a^4 + b^4 + c^4 + d^4 + 4*a*b*c*d := by

  have h3 : a^4 + b^4 + c^4 + d^4 + 4 * a * b * c * d =
      (a + b + c + d) * (a^3 + b^3 + c^3 + d^3 + a * b * c + a * b * d + a * c * d + b * c * d) - (a * b + a * c + a * d + b * c + b * d + c * d) * (a^2 + b^2 + c^2 + d^2) := by
    ring

  rw [h3] at *

  have h4 : n ∣ (a + b + c + d) * (a^3 + b^3 + c^3 + d^3 + a * b * c + a * b * d + a * c * d + b * c * d) := by
    exact dvd_mul_of_dvd_left h1 _

  have h5 : n ∣ (a * b + a * c + a * d + b * c + b * d + c * d) * (a^2 + b^2 + c^2 + d^2) := by
    exact dvd_mul_of_dvd_right h2 _

  exact Int.dvd_sub h4 h5
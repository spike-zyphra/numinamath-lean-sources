import Mathlib

theorem number_theory_239525 (n : ℤ) (hn : n > 0) (a b c d : ℤ)
    (h1 : n ∣ a + b + c + d) (h2 : n ∣ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) :
    n ∣ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 4 * a * b * c * d := by
  have h5 : a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + 4 * a * b * c * d =
    (a + b + c + d) * (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 + a * b * c + a * b * d + a * c * d + b * c * d) - (a * b + a * c + a * d + b * c + b * d + c * d) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
    ring
  rw [h5]
  apply Int.dvd_sub
  · -- Show that n divides (a + b + c + d) * (a^3 + b^3 + c^3 + d^3 + a * b * c + a * b * d + a * c * d + b * c * d)
    apply dvd_mul_of_dvd_left
    exact h1
  · -- Show that n divides (a * b + a * c + a * d + b * c + b * d + c * d) * (a^2 + b^2 + c^2 + d^2)
    apply dvd_mul_of_dvd_right
    exact h2
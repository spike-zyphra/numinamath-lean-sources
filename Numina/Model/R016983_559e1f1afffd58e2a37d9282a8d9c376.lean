import Mathlib

theorem algebra_267080 (a b : ℤ) (ha : a > 0) (hb : b > 0)
    (h : a^3 - a^2 * b + a^2 + 2 * a + 2 * b + 1 = 0) :
    (a, b) = (5, 7) := by
  have h1 : b * (a^2 - 2) = a^3 + a^2 + 2 * a + 1 := by
    nlinarith
  have h2 : a^2 - 2 ∣ a^3 + a^2 + 2 * a + 1 := by
    use b
    linarith
  have h3 : a^2 - 2 ∣ 4 * a + 3 := by
    have h4 : a^2 - 2 ∣ a^3 + a^2 + 2 * a + 1 := h2
    have h5 : a^2 - 2 ∣ (a^2 - 2) * (a + 1) := by
      apply dvd_mul_of_dvd_left
      exact dvd_refl (a^2 - 2)
    have h6 : a^3 + a^2 + 2 * a + 1 - ( (a^2 - 2) * (a + 1) ) = 4 * a + 3 := by
      nlinarith
    have h7 : a^2 - 2 ∣ (a^3 + a^2 + 2 * a + 1 - ( (a^2 - 2) * (a + 1) ) ) := by
      apply Dvd.dvd.sub
      · exact h4
      · exact h5
    rw [h6] at h7
    exact h7
  have h4 : a ≤ 5 := by
    by_contra h6
    push_neg at h6
    have h7 : a > 5 := h6
    have h8 : a^2 - 2 > 0 := by
      nlinarith
    have h5 : a^2 - 2 ≤ 4 * a + 3 := by
      apply Int.le_of_dvd (by omega) h3
    nlinarith [show a > 0 from by linarith, h7]
  have ha1 : a ≥ 1 := by
    omega
  interval_cases a <;> norm_num at h1 h3 h <;> norm_num [Prod.ext_iff] at *
  <;> omega
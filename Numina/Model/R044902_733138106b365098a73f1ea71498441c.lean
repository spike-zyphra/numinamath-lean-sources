import Mathlib

theorem number_theory_4553
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (hcoprime : Int.gcd a b = 1)
    (hdiv : a ∣ b * c) :
    a ∣ c := by
  have h1 : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hcoprime
  have h2 : a ∣ c * b := by
    have eq1 : b * c = c * b := by ring 
    have h3 : a ∣ b * c := hdiv 
    rw [eq1] at h3
    exact h3
  have h3 : a ∣ c := by
    apply h1.dvd_of_dvd_mul_right 
    exact h2 
  exact h3
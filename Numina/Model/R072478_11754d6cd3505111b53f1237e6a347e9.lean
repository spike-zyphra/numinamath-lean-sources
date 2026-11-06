import Mathlib

theorem number_theory_152020 (a b c d : ℤ) (P : ℤ → ℤ)
    (hP : ∀ x, P x = a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP1 : ∀ x, 5 ∣ P x) : 5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
  have eq1 := hP1 0
  rw [hP 0] at eq1
  have eq2 := hP1 1
  rw [hP 1] at eq2
  have eq3 := hP1 2
  rw [hP 2] at eq3
  have eq4 := hP1 3
  rw [hP 3] at eq4
  have eq5 := hP1 4
  rw [hP 4] at eq5
  have h1 : 5 ∣ d := by
    norm_num at eq1 ⊢
    exact_mod_cast eq1
  have h2 : 5 ∣ (a + b + c + d) := by
    norm_num at eq2 ⊢
    ring_nf at eq2 ⊢
    exact_mod_cast eq2
  have h3 : 5 ∣ (8 * a + 4 * b + 2 * c + d) := by
    norm_num at eq3 ⊢
    ring_nf at eq3 ⊢
    exact_mod_cast eq3
  have h4 : 5 ∣ (27 * a + 9 * b + 3 * c + d) := by
    norm_num at eq4 ⊢
    ring_nf at eq4 ⊢
    exact_mod_cast eq4
  have h5 : 5 ∣ (64 * a + 16 * b + 4 * c + d) := by
    norm_num at eq5 ⊢
    ring_nf at eq5 ⊢
    exact_mod_cast eq5
  have ha : a % 5 = 0 := by
    omega
  have hb : b % 5 = 0 := by
    omega
  have hc : c % 5 = 0 := by
    omega
  have hd : d % 5 = 0 := by
    omega
  constructor
  · exact Int.dvd_of_emod_eq_zero ha
  constructor
  · exact Int.dvd_of_emod_eq_zero hb
  constructor
  · exact Int.dvd_of_emod_eq_zero hc
  · exact Int.dvd_of_emod_eq_zero hd
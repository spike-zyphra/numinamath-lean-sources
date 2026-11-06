import Mathlib

theorem number_theory_187982 (n : ℕ) (h₀ : n ≥ 100000) (h₁ : n ≤ 999999)
    (h₂ : ∀ i, i ≥ 2 → (n / 10 ^ i) % 10 = (n / 10 ^ (i - 1)) + (n / 10 ^ (i - 2))) :
    n = 303369 := by
  have eq3 := h₂ 2 (by norm_num)
  have eq4 := h₂ 3 (by norm_num)
  have eq5 := h₂ 4 (by norm_num)
  have eq6 := h₂ 5 (by norm_num)
  have eq7 := h₂ 6 (by norm_num)

  norm_num at eq3 eq4 eq5 eq6 eq7
  have h3 : (n / 100) % 10 = (n / 10) % 10 + n % 10 := by
    omega
  have h4 : (n / 1000) % 10 = (n / 100) % 10 + (n / 10) % 10 := by
    omega
  have h5 : (n / 10000) % 10 = (n / 1000) % 10 + (n / 100) % 10 := by
    omega
  have h6 : (n / 100000) % 10 = (n / 10000) % 10 + (n / 1000) % 10 := by
    omega
  have h7 : (n / 1000000) % 10 = (n / 100000) % 10 + (n / 10000) % 10 := by
    omega

  have h₈ : n % 10 = 9 := by
    omega
  have h₉ : (n / 10) % 10 = 6 := by
    omega
  have h_10 : (n / 100) % 10 = 3 := by
    omega
  have h_11 : (n / 1000) % 10 = 3 := by
    omega
  have h12 : (n / 10000) % 10 = 6 := by
    omega
  have h13 : (n / 100000) % 10 = 3 := by
    omega
  have h14 : n = 303369 := by
    omega
  exact h14
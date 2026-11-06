import Mathlib

theorem number_theory_197797 :
    ¬∃ n : ℕ, ∃ r : ℚ, (3^n - 2^n) * r = 3^(n + 1) - 2^(n + 1) ∧
      (3^(n + 1) - 2^(n + 1)) * r = 3^(n + 2) - 2^(n + 2) := by 
  rintro ⟨n, r, h₁, h₂⟩
  have eq1 : (3 ^ n - 2 ^ n : ℚ) * r = (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) := by
    exact_mod_cast h₁
  have eq2 : (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) * r = (3 ^ (n + 2) - 2 ^ (n + 2) : ℚ) := by
    exact_mod_cast h₂
  have eq3 : (3 : ℚ) * (3 : ℚ) ^ n - (2 : ℚ) * (2 : ℚ) ^ n = (3 ^ n - 2 ^ n : ℚ) * r := by
    have eq3' : (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) = (3 : ℚ) * (3 : ℚ) ^ n - (2 : ℚ) * (2 : ℚ) ^ n := by
      ring_nf
    linarith [eq1, eq3']
  have eq4 : (3 * (3 : ℚ) ^ n - 2 * (2 : ℚ) ^ n) * r = (9 * (3 : ℚ) ^ n - 4 * (2 : ℚ) ^ n) := by
    have eq5' : (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) = 3 * (3 : ℚ) ^ n - 2 * (2 : ℚ) ^ n := by
      ring_nf
    have eq6' : (3 ^ (n + 2) - 2 ^ (n + 2) : ℚ) = 9 * (3 : ℚ) ^ n - 4 * (2 : ℚ) ^ n := by
      ring_nf
    rw [eq5'] at eq2
    rw [eq6'] at eq2
    linarith [eq2]
  have eq5 : (9 - 3 * r) * (3 : ℚ) ^ n = (4 - 2 * r) * (2 : ℚ) ^ n := by
    nlinarith [eq4]
  have eq7 : (4 - 2 * r) * (2 : ℚ) ^ n = (6 - 3 * r) * (2 : ℚ) ^ n := by
    have eq3a : (3 - r) * (3 : ℚ) ^ n = (2 - r) * (2 : ℚ) ^ n := by
      linarith [eq3]
    have eq6a : (9 - 3 * r) * (3 : ℚ) ^ n = (6 - 3 * r) * (2 : ℚ) ^ n := by
      nlinarith [eq3a]
    nlinarith [eq5, eq6a]
  have eq8 : (4 - 2 * r : ℚ) = (6 - 3 * r : ℚ) := by
    have h9 : (2 : ℚ) ^ n > 0 := by
      apply pow_pos
      norm_num
    have h10 : (4 - 2 * r : ℚ) = (6 - 3 * r : ℚ) := by
      nlinarith [eq7, h9]
    linarith
  have hr : r = 2 := by
    linarith [eq8]
  have eq9 : (3 : ℚ) * (3 : ℚ) ^ n - (2 : ℚ) * (2 : ℚ) ^ n = (3 ^ n - 2 ^ n : ℚ) * r := by
    have eq3' : (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) = (3 : ℚ) * (3 : ℚ) ^ n - (2 : ℚ) * (2 : ℚ) ^ n := by
      ring_nf
    have eq3a : (3 ^ (n + 1) - 2 ^ (n + 1) : ℚ) = (3 ^ n - 2 ^ n : ℚ) * r := by
      linarith [eq1]
    linarith [eq3', eq3a]
  rw [hr] at eq9
  have eq10 : (3 : ℚ) * (3 : ℚ) ^ n - (2 : ℚ) * (2 : ℚ) ^ n = (3 ^ n - 2 ^ n : ℚ) * (2 : ℚ) := by
    linarith [eq9]
  have h9 : (3 : ℚ) ^ n > 0 := by
    apply pow_pos
    norm_num
  have h10 : (2 : ℚ) ^ n > 0 := by
    apply pow_pos
    norm_num
  nlinarith [eq10, h9, h10]
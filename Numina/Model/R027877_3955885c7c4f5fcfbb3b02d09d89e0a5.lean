import Mathlib

theorem algebra_249899 {a b : ℕ} (ha : a > 0) (hb : b > 0) (h : a > b)
    (h1 : (2 / 7 : ℚ) = 1 / a + 1 / b) :
    a = 28 ∧ b = 4 := by

  have h2 : (a : ℚ) > 0 := by exact_mod_cast (show a > 0 by linarith)
  have h3 : (b : ℚ) > 0 := by exact_mod_cast (show b > 0 by linarith)
  have eq1 : (2 : ℚ) * (a : ℚ) * (b : ℚ) = 7 * (b : ℚ) + 7 * (a : ℚ) := by
    field_simp at h1 ⊢
    nlinarith

  have eq2 : 2 * a * b = 7 * b + 7 * a := by
    exact_mod_cast eq1

  have eq3 : a ≤ 28 := by
    by_contra h4
    push_neg at h4
    have eq4 : b ≤ 3 := by
      nlinarith [eq2, h4]
    have eq5 : b = 1 ∨ b = 2 ∨ b = 3 := by
      omega
    rcases eq5 with (h5 | h5 | h5)
    · -- b = 1
      rw [h5] at eq2
      omega
    · -- b = 2
      rw [h5] at eq2
      omega
    · -- b = 3
      rw [h5] at eq2
      omega

  have eq4 : b ≤ 28 := by
    by_contra h4
    push_neg at h4
    have eq5 : a ≤ 3 := by
      nlinarith [eq2, h4]
    have eq6 : a = 1 ∨ a = 2 ∨ a = 3 := by
      omega
    rcases eq6 with (eq7 | eq7 | eq7)
    · -- a = 1
      rw [eq7] at eq2
      omega
    · -- a = 2
      rw [eq7] at eq2
      omega
    · -- a = 3
      rw [eq7] at eq2
      omega

  interval_cases a <;> try { 
    omega 
  }
  <;> try { 
    interval_cases b <;> omega 
  }
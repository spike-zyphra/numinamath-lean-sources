import Mathlib

theorem algebra_16976 :
    IsLeast {n | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x ≠ y ∧ (1 / x + 1 / y = (1 : ℚ) / 12) ∧ n = x + y} 49 := by
  constructor
  · -- Show 49 is achievable using x = 21, y = 28
    use 21, 28
    norm_num
  · -- Show that 49 is the least value in the set
    intro n hn
    rcases hn with ⟨x, y, hx, hy, hxy, heq, hn⟩
    by_contra h
    push_neg at h
    have heq1 : (x : ℚ) > 0 := by exact_mod_cast hx
    have heq2 : (y : ℚ) > 0 := by exact_mod_cast hy
    have eq1 : (x : ℚ) * (y : ℚ) = 12 * (x + y : ℚ) := by
      have h_eq : (1 / (x : ℚ) + 1 / (y : ℚ) : ℚ) = (1 / (12 : ℚ) : ℚ) := by
        linarith [heq]
      have h2 : (x : ℚ) ≠ 0 := by positivity
      have h3 : (y : ℚ) ≠ 0 := by positivity
      field_simp at h_eq
      linarith
    have eq2 : (x : ℕ) * (y : ℕ) = 12 * (x + y : ℕ) := by
      exact_mod_cast eq1
    have h1 : x ≤ 48 := by
      omega
    have h2 : y ≤ 48 := by
      omega
    interval_cases x <;> interval_cases y
    <;> omega
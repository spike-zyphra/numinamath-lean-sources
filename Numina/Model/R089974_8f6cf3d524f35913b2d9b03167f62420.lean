import Mathlib

theorem algebra_117970 (a b c d : ℕ) (h₀ : a + b + c + d = 53) (h₁ : max (max a b) (max c d) - min (min a b) (min c d) < 5)
    (h₂ : a + b = 2 * c) (h₃ : b + c = 2 * d) :
    b = 15 := by
  have eq1 : d = 53 - 3 * c := by
    omega
  have eq2 : b = 106 - 7 * c := by
    omega
  have eq3 : a = 9 * c - 106 := by
    omega
  have : c = 12 ∨ c = 13 ∨ c = 14 ∨ c = 15 := by
    omega
  rcases this with (h | h | h | h)
  · -- c = 12
    rw [h] at eq2 eq1 eq3
    simp [eq3, eq2, h, eq1] at h₁ h₀ h₂ h₃
    all_goals
      norm_num [min_eq_left, min_eq_right, max_eq_left, max_eq_right] at h₁
      <;> try { all_goals omega }
  · -- c = 13
    rw [h] at eq2 eq1 eq3
    simp [eq3, eq2, h, eq1] at h₁ h₀ h₂ h₃
    all_goals
      omega
  · -- c = 14
    rw [h] at eq2 eq1 eq3
    simp [eq3, eq2, h, eq1] at h₁ h₀ h₂ h₃
    all_goals
      norm_num [min_eq_left, min_eq_right, max_eq_left, max_eq_right] at h₁
      <;> try { all_goals omega }
  · -- c = 15
    rw [h] at eq2 eq1 eq3
    simp [eq3, eq2, h, eq1] at h₁ h₀ h₂ h₃
    all_goals
      norm_num [min_eq_left, min_eq_right, max_eq_left, max_eq_right] at h₁
      <;> try { all_goals omega }
import Mathlib

theorem algebra_171985 {a b c : ℤ} (h₀ : (a + b + c) ^ 2 = -(a * b + a * c + b * c))
    (h₁ : a + b ≠ 0) (h₂ : b + c ≠ 0) (h₃ : a + c ≠ 0) :
    (a + b) * (a + c) % (b + c) = 0 ∧ (a + b) * (b + c) % (a + c) = 0 ∧
    (a + c) * (b + c) % (a + b) = 0 := by

  constructor
  · -- Show that (a + b) * (a + c) % (b + c) = 0
    have eq1 : (a + b) * (a + c) = - (b + c) * (b + c + 2 * a) := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h4 : (b + c) ∣ (a + b) * (a + c) := by
      rw [eq1]
      use - (b + c + 2 * a)
      all_goals ring
    have h5 : (a + b) * (a + c) % (b + c) = 0 := by
      have h7 : (b + c) ∣ (a + b) * (a + c) := h4
      exact Int.emod_eq_zero_of_dvd h7
    exact h5

  constructor
  · -- Show that (a + b) * (b + c) % (a + c) = 0
    have eq2 : (a + b) * (b + c) = - (a + c) * (a + c + 2 * b) := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h8 : (a + c) ∣ (a + b) * (b + c) := by
      rw [eq2]
      use - (a + c + 2 * b)
      all_goals ring
    have h9 : (a + b) * (b + c) % (a + c) = 0 := by
      have h11 : (a + c) ∣ (a + b) * (b + c) := h8
      exact Int.emod_eq_zero_of_dvd h11
    exact h9

  · -- Show that (a + c) * (b + c) % (a + b) = 0
    have eq3 : (a + c) * (b + c) = - (a + b) * (a + b + 2 * c) := by
      nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    have h10 : (a + b) ∣ (a + c) * (b + c) := by
      rw [eq3]
      use - (a + b + 2 * c)
      all_goals ring
    have h11 : (a + c) * (b + c) % (a + b) = 0 := by
      have h13 : (a + b) ∣ (a + c) * (b + c) := h10
      exact Int.emod_eq_zero_of_dvd h13
    exact h11
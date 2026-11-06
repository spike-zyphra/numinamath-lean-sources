import Mathlib
open Real

theorem algebra_320940 (x y a : ℝ) (h₀ : x + y = a) (h₁ : x^3 + y^3 = a) (h₂ : x^5 + y^5 = a) :
    a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 ∨ a = 2 := by 
  have eq1 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x + y) * (x * y) := by
    ring
  rw [h₀] at eq1
  have eq2 : a = a ^ 3 - 3 * a * (x * y) := by linarith [h₁, eq1]
  have eq3 : x ^ 5 + y ^ 5 = (x + y) ^ 5 - 5 * (x + y) ^ 3 * (x * y) + 5 * (x + y) * (x * y) ^ 2 := by
    ring
  rw [h₀] at eq3
  have eq4 : a = a ^ 5 - 5 * a ^ 3 * (x * y) + 5 * a * (x * y) ^ 2 := by linarith [h₂, eq3]
  by_cases ha : a = 0
  · -- if a = 0, then 0 is a solution.
    rw [ha]
    simp
  · -- a ≠ 0, can divide by a.
    have h3 : a ≠ 0 := by
      exact ha
    -- From eq2: $a = a^3 - 3a(xy)$.
    -- Rearrange: $a - a^3 = -3a(xy)$.
    -- Since $a \neq 0$, divide by $a$: $1 - a^2 = -3(xy)$.
    have eq5 : 1 - a ^ 2 = -3 * (x * y) := by
      apply (mul_left_inj' (show a ≠ 0 by exact h3)).mp
      linarith
    have eq6 : x * y = (a ^ 2 - 1) / 3 := by 
      nlinarith
    rw [eq6] at eq4
    have eq7 : a * (a ^ 2 - 1) * (a ^ 2 - 4) = 0 := by
      nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact h3)]
    cases' (mul_eq_zero.mp eq7) with eq9 eq10
    · cases' (mul_eq_zero.mp eq9) with eq11 eq12
      · -- case $a = 0$
        exfalso
        apply ha
        linarith
      · -- case $a^2 - 1 = 0$
        have eq13 : a ^ 2 = 1 := by linarith
        have eq14 : a = 1 ∨ a = -1 := by
          rw [sq_eq_one_iff] at eq13
          tauto
        cases eq14 with
        | inl h =>
          have : a = 1 := by linarith
          simp [this]
        | inr h =>
          have : a = -1 := by linarith
          simp [this]
    · -- case $a^2 - 4 = 0$
      have eq15 : a ^ 2 = 4 := by linarith
      have eq16 : a = 2 ∨ a = -2 := by
        have h3 : a ^ 2 - 4 = 0 := by linarith
        have h4 : (a - 2) * (a + 2) = 0 := by linarith
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- a - 2 = 0
          left
          linarith
        · -- a + 2 = 0
          right
          linarith
      cases eq16 with
      | inl h =>
        have : a = 2 := by linarith
        simp [this]
      | inr h =>
        have : a = -2 := by linarith
        simp [this]
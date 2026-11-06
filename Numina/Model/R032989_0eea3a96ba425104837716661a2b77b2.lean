import Mathlib

theorem algebra_111924 {a b c : ℝ} (h₀ : a^2 + b^2 = 2 * c^2) (h₁ : a ≠ b) (h₂ : c ≠ -a)
    (h₃ : c ≠ -b) :
    ∃ k : ℤ, ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2)) / ((a - b) * (a + c) * (b + c)) = k := by
  have h4 : a - b ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h5 : a + c ≠ 0 := by
    intro h
    apply h₂
    linarith
  have h6 : b + c ≠ 0 := by
    intro h
    apply h₃
    linarith
  use 3
  have eq3 : ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2)) / ((a - b) * (a + c) * (b + c)) = (3:ℝ) := by
    have eq4 : (a + b + 2 * c) * (2 * a^2 - b^2 - c^2) = 3 / 2 * (a + b + 2 * c) * (a^2 - b^2) := by
      have h7 : c^2 = (a^2 + b^2) / 2 := by linarith
      rw [h7]
      ring
    have eq5 : a^2 - b^2 = (a - b) * (a + b) := by
      ring
    have eq6 : (a + b + 2 * c) * (2 * a^2 - b^2 - c^2) = 3 / 2 * (a + b + 2 * c) * (a - b) * (a + b) := by
      rw [eq4, eq5]
      ring
    have eq7 : ((a + b + 2 * c) * (2 * a^2 - b^2 - c^2) ) / ((a - b) * (a + c) * (b + c)) =
        (3 / 2 * (a + b + 2 * c) * (a - b) * (a + b)) / ((a - b) * (a + c) * (b + c)) := by
      rw [eq6]
    have eq8 : (3 / 2 * (a + b + 2 * c) * (a - b) * (a + b)) / ((a - b) * (a + c) * (b + c)) =
        3 / 2 * (a + b + 2 * c) * (a + b) / ((a + c) * (b + c)) := by
      have h11 : a - b ≠ 0 := h4
      field_simp [h11]
      <;> ring
    have eq9 : (a + b + 2 * c) * (a + b) = 2 * ((a + c) * (b + c)) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c),
          h₀, sq_pos_of_ne_zero (show a - b ≠ 0 by assumption),
          sq_pos_of_ne_zero (show a + c ≠ 0 by assumption),
          sq_pos_of_ne_zero (show b + c ≠ 0 by assumption)]
    have eq10 : 3 / 2 * (a + b + 2 * c) * (a + b) / ((a + c) * (b + c)) = (3:ℝ) := by
      have eq11 : (a + b + 2 * c) * (a + b) = 2 * ((a + c) * (b + c)) := eq9
      have h12 : (a + c) * (b + c) ≠ 0 := by
        apply mul_ne_zero 
        exact h5 
        exact h6 
      have eq13 : 3 / 2 * (a + b + 2 * c) * (a + b) / ((a + c) * (b + c)) = 3 := by 
        field_simp [show (a + c) * (b + c) ≠ 0 by 
          apply mul_ne_zero 
          exact h5 
          exact h6 
        ] at *
        all_goals nlinarith [eq11] 
      exact_mod_cast eq13
    -- Let's connect equations so far to finish this proof.
    rw [eq7, eq8, eq10]
  exact_mod_cast eq3
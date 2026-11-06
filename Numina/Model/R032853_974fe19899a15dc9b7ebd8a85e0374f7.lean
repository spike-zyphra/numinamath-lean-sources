import Mathlib

theorem number_theory_228604 :
    Set.Infinite {(x, y) : ℝ × ℝ | x^2 + y^2 = 1 ∧ ∃ q1 q2 : ℚ, x = q1 ∧ y = q2} := by 
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => ((1 - ((↑n : ℝ)) ^ 2) / (1 + ((↑n : ℝ)) ^ 2), (2 * ((↑n : ℝ)) ) / (1 + ((↑n : ℝ)) ^ 2)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    rcases h with ⟨hx, hy⟩
    have h1 : (n : ℝ) / (1 + (n : ℝ) ^ 2) = (m : ℝ) / (1 + (m : ℝ) ^ 2) := by
      have h1 : (1 + ((↑n : ℝ)) ^ 2) ≠ 0 := by positivity
      have h2 : (1 + ((↑m : ℝ)) ^ 2) ≠ 0 := by positivity
      field_simp [h1, h2] at *
      nlinarith
    have h2 : (n : ℝ) * (1 + (m : ℝ) ^ 2) = (m : ℝ) * (1 + (n : ℝ) ^ 2) := by
      have h3 : (1 + ((↑n : ℝ)) ^ 2) ≠ 0 := by positivity
      have h4 : (1 + ((↑m : ℝ)) ^ 2) ≠ 0 := by positivity
      have h5 : (n : ℝ) / (1 + (n : ℝ) ^ 2) = (m : ℝ) / (1 + (m : ℝ) ^ 2) := h1
      field_simp [h3, h4] at h5 ⊢
      nlinarith
    have h3 : (n : ℝ) * (1 + (m : ℝ) ^ 2) - (m : ℝ) * (1 + (n : ℝ) ^ 2) = 0 := by linarith
    have h4 : (n : ℝ) - (m : ℝ) = 0 ∨ (n : ℝ) * (m : ℝ) = 1 := by
      have h5 : (n : ℝ) * (1 + (m : ℝ) ^ 2) - (m : ℝ) * (1 + (n : ℝ) ^ 2) = 0 := h3
      have h6 : (n : ℝ) * (1 + (m : ℝ) ^ 2) - (m : ℝ) * (1 + (n : ℝ) ^ 2) = (n - m : ℝ) + (n * m * (m - n) : ℝ) := by
        nlinarith
      have h7 : (n - m : ℝ) + (n * m * (m - n) : ℝ) = 0 := by
        linarith [h5, h6]
      have h8 : (n - m : ℝ) * (1 - (n * m : ℝ)) = 0 := by
        linarith
      cases (mul_eq_zero.1 h8) with
      | inl h9 =>
        left
        linarith
      | inr h10 =>
        right
        linarith
    cases h4 with
    | inl h4 =>
      have h5 : (n : ℝ) = (m : ℝ) := by linarith
      have h6 : n = m := by
        exact_mod_cast h5
      omega
    | inr h4 =>
      have h5 : (n : ℝ) * (m : ℝ) = 1 := h4
      have h6 : n * m = 1 := by
        exact_mod_cast h5
      have h7 : n = 1 := by
        have h8 : n * m = 1 := h6
        have h9 : n ∣ 1 := by
          use m
          all_goals linarith
        have h10 : n = 1 := by
          exact Nat.eq_one_of_dvd_one h9
        exact h10
      have h8 : m = 1 := by
        have h9 : n * m = 1 := h6
        have h10 : m ∣ 1 := by
          use n
          all_goals linarith
        have h11 : m = 1 := by
          exact Nat.eq_one_of_dvd_one h10
        exact h11
      have h9 : (n : ℝ) = (m : ℝ) := by
        rw [show (n : ℝ) = 1 by exact_mod_cast h7, show (m : ℝ) = 1 by exact_mod_cast h8]
      have h10 : n = m := by
        exact_mod_cast h9
      omega
  · -- Show all points are in the set
    intro n
    have h1 : ((1 - ((↑n : ℝ)) ^ 2) / (1 + ((↑n : ℝ)) ^ 2)) ^ 2 + ((2 * ((↑n : ℝ)) ) / (1 + ((↑n : ℝ)) ^ 2)) ^ 2 = 1 := by
      have h1 : (1 + ((↑n : ℝ)) ^ 2) ≠ 0 := by positivity
      field_simp [h1]
      nlinarith
    have h2 : ∃ q1 q2 : ℚ, (1 - ((↑n : ℝ)) ^ 2) / (1 + ((↑n : ℝ)) ^ 2) = q1 ∧ (2 * ((↑n : ℝ)) ) / (1 + ((↑n : ℝ)) ^ 2) = q2 := by
      use ((1 - ((↑n : ℚ)) ^ 2) / (1 + ((↑n : ℚ)) ^ 2))
      use ((2 * ((↑n : ℚ)) ) / (1 + ((↑n : ℚ)) ^ 2))
      constructor
      · -- Show the real x-coordinate equals the rational q1.
        norm_num
      · -- Show the real y-coordinate equals the rational q2.
        norm_num
    constructor
    · exact h1
    · exact h2
import Mathlib

theorem algebra_130955 (b c : ℝ) (h : ∃ x1 x2 x3, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    (x2 - x1) * (x3 - x2) = (x3 - x1) * (x2 - x3) ∧
    (x2 - x1) * (x3 - x2) = -1) :
    b = 0 ∧ c = 0 ∨ b = 1 ∧ c = 0 ∨ b = -1 ∧ c = 0 := by
  rcases h with ⟨x1, x2, x3, h1, h2, h3, h4, h5⟩
  have eq1 : (x3 - x2) * (x2 + x3 - 2 * x1) = 0 := by
    ring_nf at h4 ⊢
    <;> nlinarith
  have eq2 : x3 - x2 ≠ 0 := by
    intro h0
    have h3' : x3 = x2 := by linarith
    tauto
  have eq3 : x2 + x3 = 2 * x1 := by
    apply (mul_left_inj' eq2).mp
    linarith
  have eq4 : x3 = 2 * x1 - x2 := by
    linarith
  have eq5 : (x2 - x1) ^ 2 = 1 / 2 := by
    rw [eq4] at h5
    have h7 : (2 * x1 - x2 - x2) = 2 * (x1 - x2) := by ring
    nlinarith [sq_pos_of_ne_zero (show (x2 - x1) ≠ 0 by
      intro h0
      have h0' : x2 = x1 := by linarith
      tauto
    ), sq_pos_of_ne_zero (show x3 - x2 ≠ 0 by
      intro h0
      have h3' : x3 = x2 := by linarith
      tauto
    ), sq_pos_of_ne_zero (show (x2 - x1) ≠ 0 by
      intro h0
      have h0' : x2 = x1 := by linarith
      tauto
    )
    ]
  norm_num at eq5
  all_goals
    nlinarith [sq_nonneg (x1 - x2), sq_nonneg (x2 - x1), sq_nonneg (x3 - x1)]
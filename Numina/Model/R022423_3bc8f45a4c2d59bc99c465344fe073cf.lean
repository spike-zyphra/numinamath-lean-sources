import Mathlib

open Set Real

theorem algebra_11046 {P : Set ℝ} (hP : P = {x | abs (x + 3) + abs (x + 6) = 3}) :
    Pᶜ = {x | x < -6 ∨ x > -3} := by
  ext x
  simp [hP, Set.mem_compl_iff]
  constructor
  · -- Assume x ∉ P, prove x < -6 ∨ x > -3
    intro h
    by_contra h1
    push_neg at h1
    have h2 : abs (x + 3) + abs (x + 6) = 3 := by
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      all_goals linarith
    contradiction
  · -- Assume x < -6 ∨ x > -3, prove x ∉ P
    rintro (h1 | h2)
    · -- Assume x < -6
      have h3 : abs (x + 3) + abs (x + 6) ≠ 3 := by
        have h4 : abs (x + 3) = - (x + 3) := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        have h5 : abs (x + 6) = - (x + 6) := by
          rw [abs_of_neg]
          linarith
          all_goals linarith
        rw [h4, h5]
        intro h
        nlinarith
      intro h
      contradiction
    · -- Assume x > -3
      have h3 : abs (x + 3) + abs (x + 6) ≠ 3 := by
        have h4 : abs (x + 3) = x + 3 := by
          rw [abs_of_pos]
          linarith
          all_goals linarith
        have h5 : abs (x + 6) = x + 6 := by
          rw [abs_of_pos]
          linarith
          all_goals linarith
        rw [h4, h5]
        intro h
        nlinarith
      intro h
      contradiction
import Mathlib

theorem algebra_287162 (a : ℕ → ℝ) (h : ∀ x, (2 * x - 1) ^ 6 = ∑ i in Finset.range 7, a i * x ^ i) :
    ∑ i in Finset.range 7, |a i| = 3 ^ 6 := by

  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  have eq5 := h 4
  have eq6 := h 5
  have eq7 := h 6

  norm_num [Finset.sum_range_succ] at eq1 eq2 eq3 eq4 eq5 eq6 eq7

  have h1 : |a 0| = 1 := by
    rw [show a 0 = 1 by linarith]
    norm_num

  have h2 : a 0 = 1 := by linarith
  have h3 : a 1 = -12 := by
    linarith 
  have h4 : a 2 = 60 := by
    linarith
  have h5 : a 3 = -160 := by
    linarith 
  have h6 : a 4 = 240 := by 
    linarith
  have h7 : a 5 = -192 := by 
    linarith 
  have h8 : a 6 = 64 := by 
    linarith

  have h9 : |a 1| = 12 := by
    rw [show a 1 = -12 by linarith]
    norm_num

  have h10 : |a 2| = 60 := by
    rw [show a 2 = 60 by linarith]
    norm_num

  have h11 : |a 3| = 160 := by 
    rw [show a 3 = -160 by linarith]
    norm_num

  have h12 : |a 4| = 240 := by
    rw [show a 4 = 240 by linarith]
    norm_num

  have h13 : |a 5| = 192 := by
    rw [show a 5 = -192 by linarith]
    norm_num

  have h14 : |a 6| = 64 := by 
    rw [show a 6 = 64 by linarith]
    norm_num

  simp [Finset.sum_range_succ, h1, h9, h10, h11, h12, h13, h14]
  all_goals norm_num
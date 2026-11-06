import Mathlib

theorem algebra_128946 {x y : ℕ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : (x + y) * 6 = x * 10) (h2 : (x + y) * 6 = y * z) :
    z = 15 := by
  have eq1 : 6 * x + 6 * y = 10 * x := by
    linarith [h1]
  have eq2 : 6 * y = 4 * x := by
    linarith [eq1]
  have h3 : 3 * y = 2 * x := by
    omega
  have h4 : x * 10 = y * z := by
    linarith [h1, h2]
  have h5 : 15 * y = y * z := by
    nlinarith [h3]
  have h6 : z = 15 := by
    have h7 : y ≠ 0 := hy
    by_cases h : y = 0
    · -- h : y = 0
      rw [h] at h5
      -- contradiction from y = 0 
      contradiction
    · -- h : y ≠ 0
      have : z = 15 := by
        apply (mul_left_inj' h).mp
        nlinarith [h5]
        -- linarith
      assumption
  exact h6
  all_goals linarith
  all_goals tauto
  all_goals omega
  all_goals nlinarith
  all_goals tauto
  all_goals ring
  all_goals omega
  all_goals nlinarith
  all_goals tauto
  all_goals linarith
  all_goals ring_nf
  all_goals omega
  all_goals nlinarith
  all_goals tauto
  all_goals linarith
  all_goals ring_nf
  all_goals omega
  all_goals nlinarith
  all_goals tauto
  all_goals omega
  all_goals omega
  all_goals omega
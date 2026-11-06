import Mathlib

theorem algebra_108945 (t_ab t_ac t_ad t_ab' t_ab'' t_cb' t_db' ab ac cb db cd v: ℝ) (ht_ac : t_ac = 2)
    (ht_ab : t_ab = ab / v) (ht_cb' : t_cb' = cb / (0.75*v)) (hcb : cb = ab - ac) (hac : ac = 2 * v)
    (ht_ab' : t_ab' = t_ab + 2 - 2/3) (ht_ab'₂ : t_ab' = t_ac + t_cb') (hcd : cd = 72)
    (ht_ad : t_ad = t_ac + cd/v) (hdb : db = cb - cd) (ht_db' : t_db' = db / (0.75*v))
    (ht_ab'' : t_ab'' = t_ab + 1.5 - 2/3) (ht_ab''₂ : t_ab'' = t_ad + t_db') (hv : v ≠ 0) : ab = 288 := by
  rw [ht_ab'] at ht_ab'₂
  rw [ht_ab] at ht_ab'₂
  rw [ht_ac] at ht_ab'₂
  rw [ht_cb'] at ht_ab'₂
  rw [hcb] at ht_ab'₂
  rw [hac] at ht_ab'₂
  rw [ht_ab''] at ht_ab''₂
  rw [ht_ab] at ht_ab''₂
  rw [ht_ad] at ht_ab''₂
  rw [ht_db'] at ht_ab''₂
  rw [hdb] at ht_ab''₂
  rw [hcb] at ht_ab''₂
  rw [hcd] at ht_ab''₂
  rw [hac] at ht_ab''₂

  ring_nf at ht_ab'₂ ht_ab''₂

  -- We have 2 equations from scenario 1 and 2.
  -- ht_ab'₂ : derived from first scenario
  -- ht_ab''₂ : derived from second scenario
  -- From our first equation we get ab = 6*v
  have h1 : ab = 6*v := by
    have h2 : ab * v * (9 / 4) + v ^ 2 * 3 = ab * v * 3 + v ^ 2 * (-3 / 2) := by
      field_simp [hv] at ht_ab'₂ 
      nlinarith 
      all_goals nlinarith  -- Note: trying any methods to get this equation resolved
    have h3 : ab = 6*v := by
      apply (mul_left_inj' (show (v : ℝ) ≠ 0 by assumption)).mp
      linarith
    exact h3 

  rw [h1] at ht_ab''₂ 
  -- From equation ht_ab''₂ we can now solve for v
  -- Note: us augmented straightforward equation for speed
  have h2 : v = 48 := by
    field_simp [hv] at ht_ab''₂
    nlinarith [sq_pos_of_ne_zero (show v ≠ 0 by assumption), sq_nonneg (v - 48)]
  -- Now we can solve ab from the value of v
  -- ab = 6*v = 6*48 = 288
  have h3 : ab = 288 := by
    rw [h2] at h1
    linarith 
  exact h3
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
  all_goals nlinarith
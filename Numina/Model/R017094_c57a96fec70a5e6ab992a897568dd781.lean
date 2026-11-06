import Mathlib

theorem algebra_266555 (x y z : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h : 30 / 7 = x + 1 / (y + 1 / z : ℚ)) : x + y + z = 9 := by 
  have h1 : (30 : ℚ) / 7 = x + 1 / (y + 1 / z : ℚ) := by
    exact_mod_cast h

  have h6 : x ≤ 4 := by
    by_contra h7
    push_neg at h7
    have h2 : (x : ℚ) ≥ (5 : ℚ) := by exact_mod_cast h7
    have h3 : (30 : ℚ) / 7 = (x : ℚ) + 1 / (y + 1 / (z : ℚ)) := h1
    have h4 : (1 / (y + 1 / (z : ℚ)) : ℚ) ≤ (0 : ℚ) := by
      have h6 : (30 : ℚ) / 7 < (x : ℚ) := by linarith
      linarith [show 1 / (y + 1 / z : ℚ) = (30 / 7 : ℚ) - (x : ℚ) by linarith [h3]]
    -- Denote contradiction with biconditional equation of crotical contrary specfied.
    have h7 : (1 / (y + 1 / (z : ℚ)) : ℚ) > (0 : ℚ) := by
      apply div_pos
      norm_num
      positivity
    linarith
  have hx1 : x ≥ 1 := by linarith
  have hx2 : x ≤ 4 := h6

  have h2 : x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by 
    omega

  rcases h2 with h3 | h3 | h3 | h3
  · -- x = 1
    rw [show (x : ℚ) = (1 : ℚ) by exact_mod_cast h3] at h1
    field_simp at h1
    ring_nf at h1
    norm_cast at h1
    all_goals 
      nlinarith
  · -- x = 2
    rw [show (x : ℚ) = (2 : ℚ) by exact_mod_cast h3] at h1
    field_simp at h1
    ring_nf at h1
    norm_cast at h1
    all_goals 
      nlinarith
  · -- x = 3
    rw [show (x : ℚ) = (3 : ℚ) by exact_mod_cast h3] at h1
    field_simp at h1
    ring_nf at h1
    norm_cast at h1
    all_goals 
      nlinarith
  · -- x = 4
    rw [show (x : ℚ) = (4 : ℚ) by exact_mod_cast h3] at h1
    field_simp at h1
    ring_nf at h1
    norm_cast at h1
    have h8 : y = 3 := by
      nlinarith
    have h9 : z = 2 := by
      rw [show y = 3 by linarith] at h1
      nlinarith
    omega
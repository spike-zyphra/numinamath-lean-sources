import Mathlib

theorem algebra_625221
    {a : ℝ}
    (h : a^2 - a = 7) :
    ((a - 1) / (a + 2)) * ((a^2 - 4) / (a^2 - 2 * a + 1)) / (1 / (a^2 - 1)) = 5 := by

  have h1 : a + 2 ≠ 0 := by
    -- Hence a is not equal to -2.
    by_contra ha
    have ha2 : a = -2 := by linarith
    rw [ha2] at h
    norm_num at h
  have h2 : a^2 - 2 * a + 1 ≠ 0 := by
    -- Hence a is not equal to 1, because it would make the square zero, proved as follows.
    have ha_ne_1 : a ≠ 1 := by
      -- Assume a = 1, derive a contradiction.
      by_contra ha
      rw [ha] at h
      -- Substituting a = 1 gives 1² - 1 = 7, contradiction.
      norm_num at h
    -- Now need to prove a^2 - 2*a + 1 ≠ 0
    have eq : a^2 - 2 * a + 1 = (a - 1)^2 := by
      ring
    rw [eq]
    have hne : (a - 1) ≠ 0 := by
      exact sub_ne_zero_of_ne ha_ne_1
    -- Now need to prove (a-1)^2 ≠ 0
    have hne2 : (a - 1)^2 ≠ 0 := by
      exact pow_ne_zero 2 hne
    exact hne2
  have h3 : a^2 - 1 ≠ 0 := by
    -- Hence a ≠ 1 and a ≠ -1
    -- a ≠ 1 already known from h2.a_ne_1
    by_contra ha
    have ha2 : a^2 = 1 := by linarith
    rw [show a^2 - a = a^2 - a from rfl] at h
    rw [ha2] at h
    norm_num at h
    all_goals nlinarith
  -- ((a - 1) / (a + 2)) * ((a^2 - 4) / (a^2 - 2 * a + 1)) / (1 / (a^2 - 1)) = (a - 2) * (a + 1)
  have eqn_simplify : ((a - 1) / (a + 2)) * ((a^2 - 4) / (a^2 - 2 * a + 1)) / (1 / (a^2 - 1)) = (a - 2) * (a + 1) := by
    field_simp [(show a + 2 ≠ 0 by exact h1), (show a^2 - 2 * a + 1 ≠ 0 by exact h2), (show a^2 - 1 ≠ 0 by exact h3)]
    ring_nf
    <;> field_simp [(show a + 2 ≠ 0 by exact h1), (show a^2 - 2 * a + 1 ≠ 0 by exact h2), (show a^2 - 1 ≠ 0 by exact h3)]
    <;> nlinarith
  -- Now we have solved to (a - 2) * (a + 1). Expand it to a^2 - a - 2
  rw [eqn_simplify]
  -- Now need to derive value
  have new_h : (a - 2) * (a + 1) = a^2 - a - 2 := by ring
  have h4 : a^2 - a - 2 = 5 := by
    nlinarith
  -- Conclude
  linarith [h4]
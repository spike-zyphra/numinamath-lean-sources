import Mathlib

theorem algebra_189768 (v : ℝ) (h : v > 0) (h1 : 1 / v = 45 / (v + w)) (h2 : w = 2 * v) :
    1 / w = 90 := by
  -- Note that from h1: 1 / v = 45 / (v + w)
  -- Cross-multiplying gives v + w = 45 * v
  have h3 : v + w ≠ 0 := by
    by_contra h4
    have h4' : v + w = 0 := by linarith
    have h5 : 45 / (v + w) = 0 := by
      rw [show v + w = (0 : ℝ) by linarith [h4']]
      norm_num
    -- Substitute into h1: 1 / v = 0, which is a contradiction since 1 / v > 0
    rw [h5] at h1
    have h6 : 1 / v > 0 := by positivity
    linarith  -- contradiction: 1 / v > 0 but 1 / v = 0
  -- Use field properties to handle h1
  field_simp [h3] at h1
  -- We now have v + w = 45 * v, so w = 44 * v
  have eq1 : w = 44 * v := by
    have h_nonzero : v ≠ 0 := by linarith
    have h4 : v + w = 45 * v := by
      -- Solve from the transformed h1
      nlinarith [show 0 < v from h]
    nlinarith [show 0 < v from h]
  -- But we also know from h2 that w = 2 * v
  rw [show w = 2 * v by linarith [h2]] at eq1
  -- Therefore: 2v = 44v, so v = 0, which contradicts h: v > 0
  have h4 : v = 0 := by
    nlinarith  -- Solve for v
  linarith  -- Contradiction: v > 0 and v = 0
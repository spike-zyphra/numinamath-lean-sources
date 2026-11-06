import Mathlib

theorem algebra_243971 (f : ℝ → ℝ) (h : ∀ x y, f (2 * x - 3 * y) - f (x + y) = -2 * x + 8 * y)
    (t : ℝ) (ht : t ≠ 0) :
    (f (4 * t) - f t) / (f (3 * t) - f (2 * t)) = 3 := by
  have eq1 : f (-t) - f (2 * t) = 6 * t := by
    specialize h t t
    ring_nf at h ⊢
    all_goals linarith

  have eq2 : f t - f (3 * t) = 4 * t := by
    specialize h (2 * t) t
    ring_nf at h ⊢
    all_goals linarith

  have eq3 : f (3 * t) - f (4 * t) = 2 * t := by
    specialize h (3 * t) t
    ring_nf at h ⊢
    all_goals linarith

  have eq4 : f (2 * t) - f t = -2 * t := by
    specialize h t 0
    norm_num at h ⊢
    all_goals linarith

  have eq5 : f (4 * t) - f (2 * t) = -4 * t := by
    specialize h (2 * t) 0
    norm_num at h ⊢
    all_goals linarith

  have eq6 : f (4 * t) - f t = -6 * t := by
    nlinarith [eq2, eq3, eq4]

  have eq7 : f (3 * t) - f (2 * t) = -2 * t := by
    have eq8 : f (2 * t) = f t - 2 * t := by linarith [eq4]
    linarith [eq3, eq8]

  have eq8 : f (3 * t) - f (2 * t) ≠ 0 := by
    intro h1
    have h11 : t = 0 := by
      nlinarith [eq7, h1]
    contradiction

  have eq9 : (f (4 * t) - f t) = 3 * (f (3 * t) - f (2 * t)) := by
    linarith [eq6, eq7]

  field_simp [eq8]
  <;> linarith [eq9]
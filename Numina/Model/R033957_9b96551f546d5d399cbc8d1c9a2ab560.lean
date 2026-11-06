import Mathlib

theorem other_276571 (p : ℝ) (hp : p ∈ Set.Icc 0 1) (h : 60 / (80 / 100 * (1 - p)) = 20 / (15 / 100 * p)) :
    p = 0.64 := by
  rcases hp with ⟨hp0, hp1⟩
  have h1 : p ≠ 0 := by
    by_contra h1
    rw [h1] at h
    norm_num [h1] at h
  have h2 : 1 - p ≠ 0 := by
    by_contra h2
    have hp_eq1 : p = 1 := by linarith
    rw [hp_eq1] at h
    norm_num [hp_eq1] at h
  have eq1 : 60 / (80 / 100 * (1 - p)) = 20 / (15 / 100 * p) := h
  have eq2 : 60 * (15 / 100 * p) = 20 * (80 / 100 * (1 - p)) := by
    field_simp [(show 80 / 100 * (1 - p) ≠ 0 by
      by_contra h'
      have : 80 / 100 * (1 - p) = 0 := by linarith
      have : 1 - p = 0 := by
        nlinarith
      have h3 : p = 1 := by linarith
      tauto
    ), (show 15 / 100 * p ≠ 0 by
      by_contra h'
      have : 15 / 100 * p = 0 := by linarith
      have : p = 0 := by
        nlinarith
      contradiction
    )] at eq1 ⊢
    linarith [eq1]
  have eq3 : 60 * (15 / 100 * p) = 20 * (80 / 100 * (1 - p)) := eq2
  ring_nf at eq3 ⊢
  linarith
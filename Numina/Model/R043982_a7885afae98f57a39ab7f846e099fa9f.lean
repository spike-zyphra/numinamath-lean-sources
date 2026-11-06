import Mathlib


theorem algebra_284694 {α β : ℝ} (h : α ≠ β) (h1 : (1 / (α^2 - 10 * α - 29) + 1 / (α^2 - 10 * α - 45) - 2 / (α^2 - 10 * α - 69)) = 0)
    (h2 : (1 / (β^2 - 10 * β - 29) + 1 / (β^2 - 10 * β - 45) - 2 / (β^2 - 10 * β - 69)) = 0) :
    α + β = 10 := by

  have hα1 : α^2 - 10 * α - 29 ≠ 0 := by
    by_contra h3
    have h3' : α^2 - 10 * α - 29 = 0 := by linarith
    rw [h3'] at h1
    have h4 : α^2 - 10 * α - 45 ≠ 0 := by
      by_contra h4
      have h4' : α^2 - 10 * α - 45 = 0 := by linarith
      nlinarith
    have h5 : α^2 - 10 * α - 69 ≠ 0 := by
      by_contra h5
      have h5' : α^2 - 10 * α - 69 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h1
    all_goals
    nlinarith

  have hα2 : α^2 - 10 * α - 45 ≠ 0 := by
    by_contra h3
    have h3' : α^2 - 10 * α - 45 = 0 := by linarith
    rw [h3'] at h1
    have h4 : α^2 - 10 * α - 29 ≠ 0 := by
      by_contra h4
      have h4' : α^2 - 10 * α - 29 = 0 := by linarith
      nlinarith
    have h5 : α^2 - 10 * α - 69 ≠ 0 := by
      by_contra h5
      have h5' : α^2 - 10 * α - 69 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h1
    all_goals
    nlinarith

  have hα3 : α^2 - 10 * α - 69 ≠ 0 := by
    by_contra h3
    have h3' : α^2 - 10 * α - 69 = 0 := by linarith
    rw [h3'] at h1
    have h4 : α^2 - 10 * α - 29 ≠ 0 := by
      by_contra h4
      have h4' : α^2 - 10 * α - 29 = 0 := by linarith
      nlinarith
    have h5 : α^2 - 10 * α - 45 ≠ 0 := by
      by_contra h5
      have h5' : α^2 - 10 * α - 45 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h1
    all_goals
    nlinarith

  have eq1 : (α^2 - 10 * α - 45) * (α^2 - 10 * α - 69) + (α^2 - 10 * α - 29) * (α^2 - 10 * α - 69) - 2 * (α^2 - 10 * α - 29) * (α^2 - 10 * α - 45) = 0 := by
    field_simp [hα1, hα2, hα3] at h1
    nlinarith

  have hβ1 : β^2 - 10 * β - 29 ≠ 0 := by
    by_contra h3
    have h3' : β^2 - 10 * β - 29 = 0 := by linarith
    rw [h3'] at h2
    have h4 : β^2 - 10 * β - 45 ≠ 0 := by
      by_contra h4
      have h4' : β^2 - 10 * β - 45 = 0 := by linarith
      nlinarith
    have h5 : β^2 - 10 * β - 69 ≠ 0 := by
      by_contra h5
      have h5' : β^2 - 10 * β - 69 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h2
    all_goals
    nlinarith

  have hβ2 : β^2 - 10 * β - 45 ≠ 0 := by
    by_contra h3
    have h3' : β^2 - 10 * β - 45 = 0 := by linarith
    rw [h3'] at h2
    have h4 : β^2 - 10 * β - 29 ≠ 0 := by
      by_contra h4
      have h4' : β^2 - 10 * β - 29 = 0 := by linarith
      nlinarith
    have h5 : β^2 - 10 * β - 69 ≠ 0 := by
      by_contra h5
      have h5' : β^2 - 10 * β - 69 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h2
    all_goals
    nlinarith

  have hβ3 : β^2 - 10 * β - 69 ≠ 0 := by
    by_contra h3
    have h3' : β^2 - 10 * β - 69 = 0 := by linarith
    rw [h3'] at h2
    have h4 : β^2 - 10 * β - 29 ≠ 0 := by
      by_contra h4
      have h4' : β^2 - 10 * β - 29 = 0 := by linarith
      nlinarith
    have h5 : β^2 - 10 * β - 45 ≠ 0 := by
      by_contra h5
      have h5' : β^2 - 10 * β - 45 = 0 := by linarith
      nlinarith
    field_simp [h4, h5] at h2
    all_goals
    nlinarith

  have eq2 : (β^2 - 10 * β - 45) * (β^2 - 10 * β - 69) + (β^2 - 10 * β - 29) * (β^2 - 10 * β - 69) - 2 * (β^2 - 10 * β - 29) * (β^2 - 10 * β - 45) = 0 := by
    field_simp [hβ1, hβ2, hβ3] at h2
    nlinarith

  have eq3 : α^2 - 10 * α - 39 = 0 := by
    nlinarith

  have eq4 : β^2 - 10 * β - 39 = 0 := by
    nlinarith

  -- Subtract eq3 and eq4 to get (α - β)(α + β - 10) = 0
  have eq5 : α + β = 10 := by
    have h3 : α^2 - 10 * α - 39 = 0 := eq3
    have h4 : β^2 - 10 * β - 39 = 0 := eq4
    have h5 : α^2 - 10 * α - 39 = β^2 - 10 * β - 39 := by
      linarith
    have h6 : (α - β) * (α + β - 10) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · 
      exfalso
      apply h
      linarith
    · 
      linarith

  exact eq5
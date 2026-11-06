import Mathlib

theorem algebra_105345 {x y z : ℝ} (h₀ : x ≠ -y) (h₁ : y ≠ -z) (h₂ : z ≠ -x)
    (h₃ : x * y / (x + y) = 2 / 3) (h₄ : y * z / (y + z) = 6 / 5) (h₅ : z * x / (z + x) = 3 / 4) :
    x = 1 ∧ y = 2 ∧ z = 3 := by
  have h6 : x ≠ 0 := by
    by_contra hx
    rw [hx] at h₃
    have h : (0 : ℝ) * y / (0 + y) = 0 := by
      simp
    rw [h] at h₃
    norm_num at h₃
  have h7 : y ≠ 0 := by
    by_contra hy
    rw [hy] at h₃
    have h : x * (0 : ℝ) / (x + (0 : ℝ)) = 0 := by
      simp
    rw [h] at h₃
    norm_num at h₃
  have h8 : z ≠ 0 := by
    by_contra hz
    rw [hz] at h₄
    have h : y * (0 : ℝ) / (y + (0 : ℝ)) = 0 := by
      simp
    rw [h] at h₄
    norm_num at h₄
  have h9 : x + y ≠ 0 := by
    intro h
    have h10 : x = -y := by linarith
    contradiction
  have h10 : y + z ≠ 0 := by
    intro h
    have h11 : y = -z := by linarith
    contradiction
  have h13 : z + x ≠ 0 := by
    intro h
    have h14 : z = -x := by linarith
    have h15 : z = -x := by linarith
    contradiction
  have eq1 : 1 / x + 1 / y = 3 / 2 := by
    field_simp [h9, h6, h7] at h₃ ⊢
    nlinarith
  have eq2 : 1 / y + 1 / z = 5 / 6 := by
    field_simp [h10, h7, h8] at h₄ ⊢
    nlinarith
  have eq3 : 1 / z + 1 / x = 4 / 3 := by
    field_simp [h13, h8, h6] at h₅ ⊢
    nlinarith
  have eq4 : 1 / x = 1 := by
    linarith [eq1, eq2, eq3]
  have hx1 : x = 1 := by
    field_simp [h6] at eq4 ⊢
    all_goals nlinarith
  have eq5 : 1 / y = 1 / 2 := by
    linarith [eq1, eq4]
  have hy1 : y = 2 := by
    field_simp [h7] at eq5 ⊢
    all_goals nlinarith
  have eq6 : 1 / z = 1 / 3 := by
    linarith [eq2, eq5]
  have hz1 : z = 3 := by
    field_simp [h8] at eq6 ⊢
    all_goals nlinarith
  exact ⟨hx1, hy1, hz1⟩
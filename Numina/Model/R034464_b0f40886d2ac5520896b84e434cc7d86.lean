import Mathlib

theorem algebra_187899 {b1 q : ℝ} (hq : q ≠ 0) (h1 : b1 / (1 - q) = 60) (h2 : b1 ^ 2 / (1 - q ^ 2) = 1200) :
    b1 / (1 + q) = 20 := by

  have h3 : 1 - q ≠ 0 := by
    by_contra h
    have eq1 : b1 / (1 - q) = 0 := by
      rw [h]
      norm_num
    linarith [h1, eq1]

  have h4 : 1 - q^2 ≠ 0 := by
    by_contra h
    have eq2 : b1 ^ 2 / (1 - q ^ 2) = 0 := by
      rw [h]
      norm_num
    linarith [h2, eq2]

  have eq2 : b1 ^ 2 / (1 - q ^ 2) = (b1 / (1 - q)) * (b1 / (1 + q)) := by 
    have hne1 : 1 - q ≠ 0 := h3
    have hne2 : 1 + q ≠ 0 := by
      by_contra h
      have hq2 : 1 - q^2 = 0 := by
        have h1q : q = -1 := by linarith [h]
        rw [h1q]
        norm_num
      contradiction
    field_simp [hne1, hne2]
    <;> ring_nf

  rw [eq2] at h2
  rw [h1] at h2
  have hne2 : 1 + q ≠ 0 := by
    by_contra h
    have hq2 : 1 - q^2 = 0 := by
      have h1q : q = -1 := by linarith [h]
      rw [h1q]
      norm_num
    contradiction

  field_simp [hne2] at h2 ⊢
  <;> nlinarith
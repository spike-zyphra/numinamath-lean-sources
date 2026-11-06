import Mathlib

theorem algebra_214496 {p : ℝ} (hp : p ≠ 0) (x : ℝ) (h : x * (1 + p / 100) * (1 - p / 100) = 1) :
    x = 10000 / (10000 - p ^ 2) := by
  have eq1 : x * (1 + p / 100) * (1 - p / 100) = x * (1 - p^2 / 10000) := by
    ring_nf
  rw [eq1] at h
  have eq2 : 10000 - p^2 ≠ 0 := by
    by_contra h1
    have h2 : p^2 = 10000 := by linarith
    have h3 : x * (1 - p^2 / 10000) = 0 := by
      rw [show 1 - p ^ 2 / 10000 = 0 by
        rw [show p ^ 2 = (10000 : ℝ) by linarith]
        field_simp
        <;> linarith
      ]
      norm_num
    linarith [h, h3]
  have eq3 : x * (10000 - p ^ 2) = 10000 := by
    field_simp at h ⊢
    linarith
  have eq4 : x = 10000 / (10000 - p ^ 2) := by
    field_simp [eq2]
    linarith
  exact eq4
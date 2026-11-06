import Mathlib

theorem algebra_11159 {m n p q : ℚ} (h1 : m / n = 15) (h2 : p / n = 3) (h3 : p / q = 1 / 10) :
    m / q = 1 / 2 := by
  have hn1 : n ≠ 0 := by
    by_contra h
    rw [h] at h1
    norm_num at h1
  have h1' : m = 15 * n := by
    have : m = 15 * n := by
      field_simp [hn1] at h1 ⊢
      linarith
    assumption
  have h2' : p = 3 * n := by
    have : p = 3 * n := by
      field_simp [hn1] at h2 ⊢
      linarith
    assumption
  have h4 : q ≠ 0 := by
    by_contra h
    rw [h] at h3
    norm_num at h3
  have h3' : 10 * p = q := by
    have : 10 * p = q := by
      field_simp [h4] at h3 ⊢
      linarith
    assumption
  have hq : q = 30 * n := by
    linarith [h2', h3']
  have h5 : m / q = 1 / 2 := by
    rw [h1']
    rw [hq]
    have hn2 : n ≠ 0 := hn1
    field_simp
    <;> linarith
  exact h5
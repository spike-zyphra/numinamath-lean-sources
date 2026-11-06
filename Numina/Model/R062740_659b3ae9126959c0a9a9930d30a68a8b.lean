import Mathlib

theorem algebra_93144 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h : x = 1 / y) :
    (x - 1 / x) * (y + 1 / y) = x ^ 2 - y ^ 2 := by
  have h1 : y = 1 / x := by
    field_simp [hy] at h ⊢
    nlinarith
  have h2 : 1 / x = y := by
    field_simp [hx] at h ⊢
    nlinarith
  have h3 : 1 / y = x := by 
    field_simp [hy] at h ⊢
    nlinarith
  calc
    (x - 1 / x) * (y + 1 / y) = (x - (1 / x)) * (y + (1 / y)) := by ring
    _ = (x - y) * (x + y) := by
      rw [show 1 / x = y by exact h2]
      rw [show 1 / y = x by exact h3]
      all_goals ring
    _ = x ^ 2 - y ^ 2 := by ring
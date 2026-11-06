import Mathlib

theorem algebra_1513 {M N X : ℝ} (hM : M ≠ 0) :
    (X * (M + N) / M - X) = (X * N / M) := by
  have eq1 : X * (M + N) / M - X = (X * N) / M := by
    have h1 : M ≠ 0 := hM
    field_simp [h1]
    ring
  linarith [eq1]
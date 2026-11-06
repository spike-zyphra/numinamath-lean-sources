import Mathlib

theorem algebra_200258 {g : ℝ → ℝ} {a b c d: ℝ} {A x0: ℝ} (hA: A ≠ 0)
(hg : ∀ x: ℝ, g x = A * (x - x0) ^ 2) (hac : a ≠ c)
(h: ∃! x, g (a * x + b) + g (c * x + d) = 0): x0 = (a * d - b * c) / (a - c) := by
  rcases h with ⟨x1, ⟨hx1, h1⟩⟩
  have h2 : g (a * x1 + b) + g (c * x1 + d) = 0:= hx1
  simp [hg] at h2
  have h3 : (a * x1 + b - x0) ^ 2 + (c * x1 + d - x0) ^ 2 = 0:= by
    have : A * ((a * x1 + b - x0) ^ 2 + (c * x1 + d - x0) ^ 2) = 0 := by linarith
    have : (a * x1 + b - x0) ^ 2 + (c * x1 + d - x0) ^ 2 = 0 := by
      apply (mul_left_inj' hA).mp
      linarith
    assumption
  have h4 : (a * x1 + b - x0) ^ 2 = 0 := by nlinarith [sq_nonneg (a * x1 + b - x0), sq_nonneg (c * x1 + d - x0)]
  have h5 : (c * x1 + d - x0) ^ 2 = 0 := by nlinarith [sq_nonneg (a * x1 + b - x0), sq_nonneg (c * x1 + d - x0)]
  have ha1 : a * x1 + b - x0 = 0 := by
    rw [sq_eq_zero_iff] at h4
    linarith
  have ha2 : c * x1 + d - x0 = 0 := by
    rw [sq_eq_zero_iff] at h5
    linarith
  have eq1 : x0 = a * x1 + b := by linarith [ha1]
  have eq2 : x0 = c * x1 + d := by linarith [ha2]
  have eq4 : x0 = (a * d - b * c) / (a - c) := by
    have h2 : a - c ≠ 0 := by
      intro h
      apply hac
      linarith
    have eq3 : (a - c) * x1 = d - b := by
      linarith [eq1, eq2]
    have eq5 : x1 = (d - b) / (a - c) := by
      field_simp [h2]
      linarith [eq3]
    rw [eq1]
    rw [eq5]
    field_simp [h2]
    <;> ring
  exact_mod_cast eq4
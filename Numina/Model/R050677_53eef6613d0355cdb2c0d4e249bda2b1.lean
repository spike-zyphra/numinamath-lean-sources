import Mathlib
open Set

theorem algebra_1468 {f : ℝ → ℝ} (hf : ∀ x ∈ Ioi 0, f (2 * x) = 2 / (2 + x)) :
    ∀ x ∈ Ioi 0, 2 * f x = 8 / (4 + x) := by
  intro x hx
  have hx' : x > 0 := hx
  have h1 : f x = 4 / (4 + x) := by
    have h2 := hf (x / 2) (by
      simp at *
      all_goals
        linarith
      )
    have h3 : 2 * (x / 2 : ℝ) = x := by ring
    rw [h3] at h2
    have eq2 : f x = 4 / (4 + x) := by
      rw [h2]
      field_simp
      <;> ring_nf
      <;> field_simp
      <;> linarith
    exact eq2
  rw [show f x = 4 / (4 + x) by linarith [h1]
  ]
  field_simp
  <;> ring_nf
  <;> field_simp
  <;> linarith
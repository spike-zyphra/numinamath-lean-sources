import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_20352 (g : ℝ → ℝ) (hg : g = λ x => (3 * x + 1) / (x + 8)) :
    range g = {y | y ≠ 3} := by
  ext y
  simp [hg, mem_range]
  constructor
  · -- Assume y in range g, show y ≠ 3
    rintro ⟨x, hx⟩
    by_contra h
    rw [h] at hx
    have h1 : x + 8 ≠ 0 := by
      by_contra h2
      have hx2 : x = -8 := by linarith
      rw [hx2] at hx
      norm_num [h2] at hx
    field_simp [h1] at hx
    all_goals linarith
  · -- Assume y ≠ 3, show y in range g
    intro hy
    use (8 * y - 1) / (3 - y)
    have h2 : 3 - y ≠ 0 := by
      intro h
      have : y = 3 := by linarith
      contradiction
    field_simp [h2]
    <;> ring_nf <;> tauto
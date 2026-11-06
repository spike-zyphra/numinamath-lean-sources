import Mathlib

theorem algebra_7979 {f g : Polynomial ℝ} (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g) ≠ 0 ∧ (f * g).degree = f.degree + g.degree := by
  constructor
  · -- Show that f * g ≠ 0
    apply mul_ne_zero
    exact hf
    exact hg
  · -- Show that (f * g).degree = f.degree + g.degree
    rw [Polynomial.degree_mul]
    all_goals try { try { tauto } }
    all_goals try { try { norm_num } }
    all_goals try { try { linarith } }
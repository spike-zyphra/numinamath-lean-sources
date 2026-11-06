import Mathlib

theorem algebra_109871 {x : ℕ → ℝ} (hx : x 0 = a) (hx' : x 1 = b)
    (h : ∀ n, x (n + 2) = x (n + 1) - x n) :
    x 99 = -a ∧ ∑ i in Finset.range 100, x i = 2 * b - a := by

  have h1 : x 0 = a := hx
  have h2 : x 1 = b := hx'

  have eq1 : x 2 = b - a := by
    specialize h 0
    norm_num [h1, h2] at h ⊢
    linarith

  have eq2 : x 3 = -a := by
    specialize h 1
    norm_num [h2, eq1] at h ⊢
    linarith

  have eq3 : x 4 = -b := by
    specialize h 2
    norm_num [eq1, eq2] at h ⊢
    linarith

  have eq4 : x 5 = a - b := by 
    specialize h 3
    norm_num [eq2, eq3] at h ⊢
    linarith

  have eq5 : x 6 = a := by 
    specialize h 4
    norm_num [eq3, eq4] at h ⊢
    linarith

  have hx99 : x 99 = -a := by
    norm_num [h1, h2, eq1, eq2, eq3, eq4, eq5, h]

  have eq7 : ∑ i in Finset.range 100, x i = 2 * b - a := by 
    norm_num [Finset.sum_range_succ, h1, h2, eq1, eq2, eq3, eq4, eq5, h]
    <;> linarith

  constructor 
  · exact hx99
  · exact eq7
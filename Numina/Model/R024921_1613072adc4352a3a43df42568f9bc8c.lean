import Mathlib

open Polynomial

theorem algebra_19853 {h g : Polynomial ℝ} (hdeg : h.natDegree = 5)
    (hgh : h = (X ^ 2 - 7 * X + 10) * g) :
    g.natDegree = 3 := by
  rw [hgh] at hdeg
  have h1 : h = (X ^ 2 - 7 * X + 10) * g := by
    simpa using hgh

  have h2 : ((X ^ 2 - 7 * X + 10 : Polynomial ℝ) * g).natDegree = (X ^ 2 - 7 * X + 10 : Polynomial ℝ).natDegree + g.natDegree := by
    apply natDegree_mul
    all_goals
    try { 
      have h11 : (X ^ 2 - 7 * X + 10 : Polynomial ℝ) ≠ 0 := by
        intro h'
        have eq1 := congr_arg (fun f => f.eval 0) h'
        simp at eq1
        all_goals nlinarith
      exact h11
    }
    try { 
      by_contra h'
      rw [h'] at hdeg
      simp at hdeg
      all_goals nlinarith
    }
  have h3 : (X ^ 2 - 7 * X + 10 : Polynomial ℝ).natDegree = 2 := by
    compute_degree <;> norm_num

  have eq1 : (X ^ 2 - 7 * X + 10 : Polynomial ℝ).natDegree + g.natDegree = 5 := by
    nlinarith [hdeg, h2]

  nlinarith [eq1, h3]
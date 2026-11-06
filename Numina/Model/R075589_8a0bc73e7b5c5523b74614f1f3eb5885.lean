import Mathlib

theorem algebra_314626 {f : ℝ → ℝ} (hf : ∃ a : Fin 5 → ℝ, f = fun x => a 0 * x ^ 4 + a 1 * x ^ 3 + a 2 * x ^ 2 + a 3 * x + a 4)
    (h1 : f 1 = 0) (h2 : f 2 = 0) (h3 : f 3 = 0) (h4 : f 4 = 6) (h5 : f 5 = 72) :
    f = fun x => (x - 1) * (x - 2) * (x - 3) * (2 * x - 7) := by 
  rcases hf with ⟨a, rfl⟩
  have eq1 := h1 
  simp [Fin.sum_univ_five] at eq1
  have eq2 := h2
  simp [Fin.sum_univ_five] at eq2
  have eq3 := h3
  simp [Fin.sum_univ_five] at eq3
  have eq4 := h4
  simp [Fin.sum_univ_five] at eq4
  have eq5 := h5
  simp [Fin.sum_univ_five] at eq5
  funext x 
  have eq6 : a 0 * x ^ 4 + a 1 * x ^ 3 + a 2 * x ^ 2 + a 3 * x + a 4 = 
            (x - 1) * (x - 2) * (x - 3) * (2 * x - 7) := by 
    ring_nf
    have ha0 : a 0 = 2 := by 
      linarith [eq1, eq2, eq3, eq4, eq5]
    have ha1 : a 1 = -19 := by 
      linarith [eq1, eq2, eq3, eq4, eq5]
    have ha2 : a 2 = 64 := by 
      linarith [eq1, eq2, eq3, eq4, eq5]
    have ha3 : a 3 = -89 := by 
      linarith [eq1, eq2, eq3, eq4, eq5]
    have ha4 : a 4 = 42 := by 
      linarith [eq1, eq2, eq3, eq4, eq5]
    rw [ha0, ha1, ha2, ha3, ha4]
    <;> ring
  exact eq6
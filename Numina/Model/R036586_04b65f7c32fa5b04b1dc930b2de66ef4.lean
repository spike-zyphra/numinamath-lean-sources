import Mathlib

theorem algebra_157859 {P : Polynomial ℤ} (hP : P.degree = 6)
    (hP1 : ∀ n ∈ Finset.range 7, P.coeff n = 1 ∨ P.coeff n = -1) (hP2 : P.eval 2 = 27) :
    P.eval 3 = 439 := by
  have h1 := hP1 0 (by simp)
  have h2 := hP1 1 (by simp)
  have h3 := hP1 2 (by simp)
  have h4 := hP1 3 (by simp)
  have h5 := hP1 4 (by simp)
  have h6 := hP1 5 (by simp)
  have h7 := hP1 6 (by simp)
  have eq1 : P.eval 2 = 64 * P.coeff 6 + 32 * P.coeff 5 + 16 * P.coeff 4 + 8 * P.coeff 3 + 4 * P.coeff 2 + 2 * P.coeff 1 + P.coeff 0 := by
    have h8 : P.natDegree = 6 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
      all_goals linarith 
    simp [Polynomial.eval_eq_sum_range, h8, Finset.sum_range_succ]
    <;> ring_nf <;> norm_num
    all_goals try linarith 
    all_goals try ring_nf <;> norm_num 
    all_goals try linarith 
  have eq2 : P.eval 3 = 729 * P.coeff 6 + 243 * P.coeff 5 + 81 * P.coeff 4 + 27 * P.coeff 3 + 9 * P.coeff 2 + 3 * P.coeff 1 + P.coeff 0 := by
    have h8 : P.natDegree = 6 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hP]
      all_goals linarith 
    simp [Polynomial.eval_eq_sum_range, h8, Finset.sum_range_succ]
    <;> ring_nf <;> norm_num
    all_goals try linarith 
    all_goals try ring_nf <;> norm_num 
    all_goals try linarith 
  rw [eq1] at hP2
  rw [eq2] at *
  have h1' : P.coeff 0 = 1 ∨ P.coeff 0 = -1 := h1
  have h2' : P.coeff 1 = 1 ∨ P.coeff 1 = -1 := h2
  have h3' : P.coeff 2 = 1 ∨ P.coeff 2 = -1 := h3
  have h4' : P.coeff 3 = 1 ∨ P.coeff 3 = -1 := h4
  have h5' : P.coeff 4 = 1 ∨ P.coeff 4 = -1 := h5
  have h6' : P.coeff 5 = 1 ∨ P.coeff 5 = -1 := h6
  have h7' : P.coeff 6 = 1 ∨ P.coeff 6 = -1 := h7
  rcases h1' with (h1' | h1') <;> rcases h2' with (h2' | h2') <;> rcases h3' with (h3' | h3') <;> rcases h4' with (h4' | h4') <;> rcases h5' with (h5' | h5') <;> rcases h6' with (h6' | h6') <;> rcases h7' with (h7' | h7') <;> omega 
  all_goals linarith
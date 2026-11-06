import Mathlib

theorem number_theory_83020 {f : Polynomial ℤ} (hf : f.degree = 2)
    (h : ∀ k : ℤ, 5 ∣ f.eval k) : ∀ n : Fin 3, 5 ∣ f.coeff n := by
  have h0 : 5 ∣ f.eval 0 := h 0
  have h1 : 5 ∣ f.eval 1 := h 1
  have h2 : 5 ∣ f.eval 2 := h 2
  have h3 : 5 ∣ f.eval 3 := h 3
  have h4 : 5 ∣ f.eval 4 := h 4

  have eq0 : f.eval 0 = f.coeff 0 := by 
    have h9 : f.natDegree = 2 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    simp [Polynomial.eval_eq_sum_range, h9, Finset.sum_range_succ]
  
  have eq1 : f.eval 1 = f.coeff 0 + f.coeff 1 + f.coeff 2 := by 
    have h9 : f.natDegree = 2 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    simp [Polynomial.eval_eq_sum_range, h9, Finset.sum_range_succ]
    <;> ring
  
  have eq2 : f.eval 2 = f.coeff 0 + 2 * f.coeff 1 + 4 * f.coeff 2 := by 
    have h9 : f.natDegree = 2 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    simp [Polynomial.eval_eq_sum_range, h9, Finset.sum_range_succ]
    <;> ring
  
  have eq3 : f.eval 3 = f.coeff 0 + 3 * f.coeff 1 + 9 * f.coeff 2 := by 
    have h9 : f.natDegree = 2 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    simp [Polynomial.eval_eq_sum_range, h9, Finset.sum_range_succ]
    <;> ring
  
  have eq4 : f.eval 4 = f.coeff 0 + 4 * f.coeff 1 + 16 * f.coeff 2 := by 
    have h9 : f.natDegree = 2 := by 
      rw [Polynomial.natDegree_eq_of_degree_eq_some hf]
    simp [Polynomial.eval_eq_sum_range, h9, Finset.sum_range_succ]
    <;> ring
  
  have hc0 : 5 ∣ f.coeff 0 := by 
    have eq00 : f.eval 0 = f.coeff 0 := eq0
    rw [eq00] at h0
    exact h0
  
  have hc1 : 5 ∣ (f.coeff 0 + f.coeff 1 + f.coeff 2) := by 
    have eq11 : f.eval 1 = f.coeff 0 + f.coeff 1 + f.coeff 2 := eq1
    rw [eq11] at h1 
    exact h1
  
  have hc2 : 5 ∣ (f.coeff 0 + 2 * f.coeff 1 + 4 * f.coeff 2) := by 
    have eq22 : f.eval 2 = f.coeff 0 + 2 * f.coeff 1 + 4 * f.coeff 2 := eq2
    rw [eq22] at h2 
    exact h2
  
  have hc3 : 5 ∣ (f.coeff 0 + 3 * f.coeff 1 + 9 * f.coeff 2) := by 
    have eq33 : f.eval 3 = f.coeff 0 + 3 * f.coeff 1 + 9 * f.coeff 2 := eq3
    rw [eq33] at h3 
    exact h3
  
  have hc4 : 5 ∣ (f.coeff 0 + 4 * f.coeff 1 + 16 * f.coeff 2) := by 
    have eq44 : f.eval 4 = f.coeff 0 + 4 * f.coeff 1 + 16 * f.coeff 2 := eq4
    rw [eq44] at h4 
    exact h4
  
  have h7 : 5 ∣ f.coeff 1 := by
    omega
  
  have h8 : 5 ∣ f.coeff 2 := by
    omega
  
  intro n
  fin_cases n <;> simp [hc0, h7, h8]
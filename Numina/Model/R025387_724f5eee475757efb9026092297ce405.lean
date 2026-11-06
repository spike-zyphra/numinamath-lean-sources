import Mathlib

theorem algebra_61330 {P : Polynomial ℝ} (hP : P.degree ≤ 6)
    (hP1 : ∀ k ∈ Finset.range 7, P.eval (k : ℝ) = Nat.factorial k) :
    P.eval 7 = 3186 := by
  have eq1 := hP1 0 (Finset.mem_range.mpr (by norm_num))
  have eq2 := hP1 1 (Finset.mem_range.mpr (by norm_num))
  have eq3 := hP1 2 (Finset.mem_range.mpr (by norm_num))
  have eq4 := hP1 3 (Finset.mem_range.mpr (by norm_num))
  have eq5 := hP1 4 (Finset.mem_range.mpr (by norm_num))
  have eq6 := hP1 5 (Finset.mem_range.mpr (by norm_num))
  have eq7 := hP1 6 (Finset.mem_range.mpr (by norm_num))
  have h8 : P.natDegree ≤ 6 := by
    rw [Polynomial.natDegree_le_iff_degree_le] 
    exact hP
  have h10 : P.natDegree ≤ 6 := h8
  have h11 : P.natDegree ≥ 0 := by apply Nat.zero_le
  have h9 : P.eval 7 = (∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * (7 : ℝ) ^ i) := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  rw [h9]
  have eq1' : P.eval (0 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((0 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq2' : P.eval (1 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((1 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq3' : P.eval (2 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((2 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq4' : P.eval (3 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((3 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq5' : P.eval (4 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((4 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq6' : P.eval (5 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((5 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  have eq7' : P.eval (6 : ℝ) = ∑ i in Finset.range (P.natDegree + 1), (P.coeff i) * ((6 : ℝ) : ℝ) ^ i := by
    simp [Polynomial.eval_eq_sum_range, h8]
    <;> try tauto
  simp [Nat.factorial] at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  simp [eq1'] at eq1
  simp [eq2'] at eq2
  simp [eq3'] at eq3
  simp [eq4'] at eq4
  simp [eq5'] at eq5
  simp [eq6'] at eq6
  simp [eq7'] at eq7
  have h14 : P.natDegree ≤ 6 := h8
  have h11 : P.natDegree ≥ 0 := by apply Nat.zero_le
  interval_cases P.natDegree <;> norm_num [Finset.sum_range_succ] at *
  <;> norm_num
  all_goals try { 
    linarith
  }
  all_goals try { 
    simp_all [Nat.factorial, Finset.sum_range_succ, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  }
  <;> norm_num
  <;> nlinarith
  <;> norm_num
  -- Use Lagrange interpolation form of P(x) then compute P(7)
  all_goals try { 
    tauto
    <;> nlinarith
  }
import Mathlib

theorem number_theory_153421 :
    ¬∃ P : Polynomial ℤ, P.degree = 2 ∧
    (∀ x : ℤ, x ≡ 1 [ZMOD 2] → P.eval x ≡ 0 [ZMOD 8]) ∧
    (∀ x : ℤ, x ≡ 0 [ZMOD 2] → P.eval x ≡ 1 [ZMOD 8]) := by
  rintro ⟨P, hPdeg, hP1, hP0⟩
  have h0 := hP0 0 (by simp [Int.ModEq])
  have h1 := hP1 1 (by simp [Int.ModEq])
  have h2 := hP0 2 (by simp [Int.ModEq])
  have h3 := hP1 3 (by simp [Int.ModEq])
  have h4 : P.eval 0 % 8 = 1 := by
    simp [Int.ModEq] at h0 ⊢
    omega
  have h5 : P.eval 1 % 8 = 0 := by
    simp [Int.ModEq] at h1 ⊢
    omega
  have h6 : P.eval 2 % 8 = 1 := by
    simp [Int.ModEq] at h2 ⊢
    omega
  have h7 : P.eval 3 % 8 = 0 := by
    simp [Int.ModEq] at h3 ⊢
    omega
  have h8 : P.natDegree = 2 := by
    rw [Polynomial.natDegree_eq_of_degree_eq_some hPdeg]
    all_goals
      norm_num
  have h9 : ∀ x : ℤ, P.eval x = (P.coeff 2) * x^2 + (P.coeff 1) * x + (P.coeff 0) := by
    intro x
    simp [Polynomial.eval_eq_sum_range, h8, Finset.sum_range_succ, mul_add, mul_comm]
    <;> ring
  have eq1 := h9 0
  have eq2 := h9 1
  have eq3 := h9 2
  have eq4 := h9 3
  simp at eq1 eq2 eq3 eq4
  simp [eq1] at h4
  simp [eq2] at h5
  simp [eq3] at h6
  simp [eq4] at h7
  omega
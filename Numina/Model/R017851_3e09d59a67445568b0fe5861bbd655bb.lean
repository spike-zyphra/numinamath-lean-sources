import Mathlib

theorem algebra_30029 {P : Polynomial ℝ} (hP : P.eval 0 = 1)
    (hP' : ∀ i, P.coeff i ≠ 0 → P.coeff i = 1 ∨ P.coeff i = -1)
    (hP'' : ∀ i, P.coeff i ≠ 0 → P.coeff i = 1 → P.coeff (i + 1) ≠ 0 ∧ P.coeff (i + 1) = -1)
    (hP''' : ∀ i, P.coeff i ≠ 0 → P.coeff i = -1 → P.coeff (i + 1) ≠ 0 ∧ P.coeff (i + 1) = 1)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : Nat.Coprime m n) :
    ∃ Q : Polynomial ℝ, Q.eval 0 = 1 ∧
      (∀ i, Q.coeff i ≠ 0 → Q.coeff i = 1 ∨ Q.coeff i = -1) ∧
      (∀ i, Q.coeff i ≠ 0 → Q.coeff i = 1 → Q.coeff (i + 1) ≠ 0 ∧ Q.coeff (i + 1) = -1) ∧
      (∀ i, Q.coeff i ≠ 0 → Q.coeff i = -1 → Q.coeff (i + 1) ≠ 0 ∧ Q.coeff (i + 1) = 1) ∧
      Q = P.comp (X ^ n) * ((X ^ (m * n) - 1) * (X - 1)) / ((X ^ m - 1) * (X ^ n - 1)) := by 
  -- h1 : The coefficient of x^{natDegree+1} is 0.
  have h1 : P.coeff (P.natDegree + 1) = 0 := by
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    linarith
  -- h2 : ∀ (i : ℕ), P.coeff i ≠ 0 → ∀ (k : ℕ), P.coeff (i + k) ≠ 0.
  have h2 : ∀ (i : ℕ), P.coeff i ≠ 0 → ∀ (k : ℕ), P.coeff (i + k) ≠ 0 := by
    intro i h
    intro k
    induction k with
    | zero => 
      simpa 
    | succ k ih =>
      have h3 : P.coeff (i + k) ≠ 0 := ih
      have h4 : P.coeff (i + k) = 1 ∨ P.coeff (i + k) = -1 := hP' (i + k) (show P.coeff (i + k) ≠ 0 by simpa using h3)
      cases h4 with
      | inl h4 =>
        have h5 : P.coeff (i + k + 1) ≠ 0 := by
          have h7 : P.coeff (i + k + 1) ≠ 0 := (hP'' (i + k) (by simpa using h3) (by simpa using h4)).1
          simpa using h7
        simpa using h5
      | inr h4 =>
        have h5 : P.coeff (i + k + 1) ≠ 0 := by
          have h7 : P.coeff (i + k + 1) ≠ 0 := (hP''' (i + k) (by simpa using h3) (by simpa using h4)).1
          simpa using h7
        simpa using h5
  have h8 : P.coeff 0 = 1 := by
    have h10 : P.eval 0 = 1 := hP
    simp [Polynomial.eval] at h10 ⊢
    all_goals linarith
  have h9 : P.coeff 0 ≠ 0 := by 
    rw [h8]
    norm_num
  have h11 : ∀ (k : ℕ), P.coeff (0 + k) ≠ 0 := h2 0 h9 
  have h12 : P.coeff (P.natDegree + 1) ≠ 0 := by 
    have h13 : P.coeff (0 + (P.natDegree + 1)) ≠ 0 := h11 (P.natDegree + 1)
    simpa using h13 
  -- Contradicts to h1 : P.coeff (P.natDegree + 1) = 0.
  exfalso 
  tauto
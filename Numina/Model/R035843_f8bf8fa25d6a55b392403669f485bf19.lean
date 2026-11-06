import Mathlib

theorem algebra_6670 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {k : ℝ} (hk : k ≠ 1 ∧ k ≠ -1) (hA : A = k • A.transpose) : A = 0 := by
  have hk1 : k ≠ 1 := hk.1
  have hk2 : k ≠ -1 := hk.2
  have eq1 : ∀ i j : Fin n, A i j = k * A j i := by 
    intro i j
    have eq2 : A i j = k * A j i := by 
      have h1 := congr_arg (λ M => M i j) hA
      simp [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h1 ⊢
      linarith
    exact eq2
  have eq2 : ∀ i j : Fin n, A i j = 0 := by 
    intro i j 
    have eq3 : A i j = k * A j i := eq1 i j 
    have eq4 : A j i = k * A i j := eq1 j i 
    have eq5 : A i j = k ^ 2 * A i j := by 
      calc
        A i j = k * A j i := eq3
        _ = k * (k * A i j) := by rw [eq4] 
        _ = k ^ 2 * A i j := by ring
    have eq6 : (1 - k ^ 2) * (A i j) = 0 := by
      linarith 
    cases' (mul_eq_zero.1 eq6) with h1 h2 
    · -- $1 - k^2 = 0$
      have hk2_eq : k ^ 2 = 1 := by
        linarith 
      have hk3 : k = 1 ∨ k = -1 := by 
        have h1 : k ^ 2 - 1 = 0 := by linarith 
        have h2 : (k - 1) * (k + 1) = 0 := by
          linarith [h1]
        cases' (mul_eq_zero.1 h2) with h3 h4 
        · -- k - 1 = 0 
          left 
          linarith 
        · -- k + 1 = 0 
          right 
          linarith 
      cases' hk3 with h h 
      · -- k = 1
        exfalso
        apply hk1 
        exact h 
      · -- k = -1
        exfalso 
        apply hk2 
        linarith 
    · -- A i j = 0 
      linarith 
  have h_eq : A = (0 : Matrix (Fin n) (Fin n) ℝ) := by
    funext i j 
    exact eq2 i j 
  exact h_eq
import Mathlib

theorem algebra_7205 {n : ℕ} {n_pos : n > 0} {lambda : Fin n → ℝ}
    {D : Matrix (Fin n) (Fin n) ℝ}
    (hD_1 : ∀ i j, D i j = if i = j then lambda i else 0)
    (hD_2 : ∀ i j, i ≠ j → lambda i ≠ lambda j) :
    ∀ A : Matrix (Fin n) (Fin n) ℝ, D * A = A * D → ∃ A_l : Fin n → ℝ,
      ∀ i, A i i = A_l i ∧ ∀ i j, i ≠ j → A i j = 0 := by
  intro A hAD
  use (λ i => A i i)
  intro i
  constructor
  · -- Show that $A_{i,i}$ is equal to the diagonal of $A$.
    simp
  · -- Show that $A_{i,j}=0$ when $i≠j$.
    intro i j h_inej
    have eq1 := congr_arg (fun M => M i j) hAD
    simp [Matrix.mul_apply, hD_1, Fin.sum_univ_three, mul_add, add_mul] at eq1 
    have h1 : A i j * (lambda j - lambda i) = 0 := by 
      linarith 
    have h2 : (lambda j - lambda i) ≠ 0 := by
      by_contra hzero 
      have heq : lambda j = lambda i := by linarith
      have heq2 : lambda i = lambda j := by linarith [heq]
      have hneq : lambda i ≠ lambda j := hD_2 i j h_inej
      contradiction 
    have h3 : A i j = 0 := by
      apply_fun (λ x => x / (lambda j - lambda i)) at h1
      field_simp [h2] at h1 
      linarith 
    exact h3
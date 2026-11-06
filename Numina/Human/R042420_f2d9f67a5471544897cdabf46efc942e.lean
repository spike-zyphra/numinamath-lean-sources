import Mathlib

/- A line is parameterized by a parameter $t,$ so that the vector on the line at $t = -2$ is $\begin{pmatrix} 2 \\ -4 \end{pmatrix},$ and the vector on the line at $t = 3$ is $\begin{pmatrix} 1 \\ 7 \end{pmatrix}.$  Find the vector on the line at $t = 5.$ -/
theorem calculus_18627 (l : ℝ → ℝ × ℝ) (a d : ℝ × ℝ) (h0 : ∀ t, l t = a + t • d) (h1 : l (-2) = (2, -4)) (h2 : l 3 = (1, 7)) : l 5 = (3 / 5, 57 / 5) := by
  rw [h0] at h1
  rw [h0] at h2
  -- solve $a - 2d = (2, -4), a + 3d = (1, 7)$ we get $a + 5d = (3 / 5. 57 / 5)
  have eq1 := h1
  apply congrArg (fun x ↦ x.1) at eq1
  simp only [neg_smul, Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul] at eq1
  have eq2 := h1
  apply congrArg (fun x ↦ x.2) at eq2
  simp only [neg_smul, Prod.snd_add, Prod.snd_neg, Prod.smul_snd, smul_eq_mul] at eq2
  have eq3 := h2
  apply congrArg (fun x ↦ x.1) at eq3
  simp only [neg_smul, Prod.fst_add, Prod.fst_neg, Prod.smul_fst, smul_eq_mul] at eq3
  have eq4 := h2
  apply congrArg (fun x ↦ x.2) at eq4
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul] at eq4
  rw [h0]
  ext
  simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
  linarith
  simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  linarith
  
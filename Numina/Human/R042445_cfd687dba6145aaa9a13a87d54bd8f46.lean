import Mathlib

open Matrix

/- Given
\[\mathbf{A} = \begin{pmatrix} 3 & 7 \\ -1 & -2 \end{pmatrix},\]
compute $\mathbf{A}^{27} + \mathbf{A}^{31} + \mathbf{A}^{40}.$ -/
theorem calculus_23377 {A : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A = !![3, 7; -1, -2]) :
    A^27 + A^31 + A^40 = !![-1, 0; 0, -1] := by
  -- notice that A^2 = (2,7; -1,-3) and A^3 = -I
  have h1: A^2 = !![2,7;-1,-3] := by
    rw [hA, pow_two]
    simp; ring_nf
  have h2: A^3 = -1 := by
    rw [one_fin_two]
    rw [pow_three, ← pow_two, h1, hA]
    simp; ring_nf
  -- thus we can simplify A^27, A^31 and A^40
  have h3: (-1: Matrix (Fin 2) (Fin 2) ℝ)^2 = 1 := by simp
  -- A^27 = (A^3)^9 = -1
  have h4: A^27 = -1 := by
    have hh1: A^27 = (A^3)^9 := by
      rw [← pow_mul]
    rw [hh1, h2]
    have hh2: (-1: Matrix (Fin 2) (Fin 2) ℝ)^9 =
      ((-1)^2)^4*(-1) := by
      rw [← pow_mul]; norm_num
    rw [hh2, h3]; simp
  -- A^31 = (A^3)^10 * A = A
  have h5: A^31 = A := by
    have hh1: A^31 = A^30 * A := by rw [pow_succ]
    have hh2: A^30 = 1 := by
      have: A^30 = ((A^3)^2)^5 := by
        rw [← pow_mul, ← pow_mul]
      rw [this, h2, h3]; simp
    rw [hh1, hh2]; simp
  -- A^40 = A^39 * A = -A
  have h6: A^40 = -A := by
    have hh1: A^40 = (A^36) * A^3 * A := by
      rw [← pow_add]; norm_num
      rw [pow_succ]
    have hh2: A^36 = 1 := by
      have: A^36 = ((A^3)^2)^6 := by
        rw [← pow_mul, ← pow_mul]
      rw [this, h2, h3]; simp
    rw [hh1, hh2, h2]; simp
  -- so answer is I + A - A = I
  rw [h4, h5, h6]; simp
  rw [one_fin_two]; simp
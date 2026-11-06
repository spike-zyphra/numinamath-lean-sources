import Mathlib

open scoped Matrix

/-Let $\mathbf{a}$ and $\mathbf{b}$ be vectors, and let $\mathbf{m}$ be the midpoint of $\mathbf{a}$ and $\mathbf{b} $  Given $\mathbf{m} = \begin{pmatrix} 3 \\ 7 \end{pmatrix}$ and $\mathbf{a} \cdot \mathbf{b} = 6,$ find $\|\mathbf{a}\|^2 + \|\mathbf{b}\|^2 $-/
theorem calculus_12883
    (a b m : Fin 2 → ℝ)
    (h₀ : ∀i, m i = ((a i + b i) / 2))
    (h₁ : a 0 * b 0 + a 1 * b 1 = 6)
    (h₂ : m 0 = 3 ∧ m 1 = 7) :
    ((a 0) ^ 2 + (a 1) ^ 2) + ((b 0) ^ 2 + (b 1) ^ 2) = 220 := by
  -- Since $\mathbf{m}$ is the midpoint of $\mathbf{a}$ and $\mathbf{b},$
  -- \[\mathbf{m} = \frac{\mathbf{a} + \mathbf{b}}{2} \]
  -- Hence, $\mathbf{a} + \mathbf{b} = 2 \mathbf{m} = \begin{pmatrix} 6 \\ 14 \end{pmatrix} $
  have a_add_b : a + b = 2 * m := by
    ext i
    simp
    rw [h₀ i]
    linarith

  -- Then \[\|\mathbf{a} + \mathbf{b}\|^2 = \left\| \begin{pmatrix} 6 \\ 14 \end{pmatrix} \right\|^2 = 6^2  + 14^2 = 232 \]
  have a_add_b_dot_mul : dotProduct (a + b) (a + b) = 232 := by
    rw [a_add_b]
    simp
    rw [h₂.1, h₂.2]
    linarith
  have : a ⬝ᵥ a = a 0 ^ 2 + a 1 ^ 2 := by
    simp
    linarith
  rw [this.symm]
  have : b ⬝ᵥ b = b 0 ^ 2 + b 1 ^ 2 := by
    simp
    linarith
  rw [this.symm]
  have : a ⬝ᵥ b = a 0 * b 0 + a 1 * b 1 := by simp
  rw [this.symm] at h₁

  have : dotProduct (a + b) (a + b) = a ⬝ᵥ a + 2 * (a ⬝ᵥ b) + b ⬝ᵥ b := by
    simp
    linarith
  rw [a_add_b_dot_mul, h₁] at this
  linarith

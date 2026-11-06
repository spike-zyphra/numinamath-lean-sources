import Mathlib

open Matrix

theorem algebra_112313 {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : A ∈ {A | ∃ x : ℝ, x ≠ 0 ∧ A = !![2 - x, x - 1; 2 - 2 * x, 2 * x - 1]})
    (hB : B ∈ {B | ∃ x : ℝ, x ≠ 0 ∧ B = !![2 - x, x - 1; 2 - 2 * x, 2 * x - 1]}) :
    A ^ 2 * B ^ 2 ∈ {C | ∃ x : ℝ, x ≠ 0 ∧ C = !![2 - x, x - 1; 2 - 2 * x, 2 * x - 1]} := by
  rcases hA with ⟨x, hx, hA⟩
  rcases hB with ⟨y, hy, hB⟩
  use x ^ 2 * y ^ 2
  constructor
  · -- Show z ≠ 0
    apply mul_ne_zero
    · -- x^2 ≠ 0
      apply pow_ne_zero 2
      exact hx
    · -- y^2 ≠ 0
      apply pow_ne_zero 2
      exact hy
  · -- Show A ^ 2 * B ^ 2 = !![2 - x ^ 2 * y ^ 2, x ^ 2 * y ^ 2 - 1; 2 - 2 * (x ^ 2 * y ^ 2), 2 * (x ^ 2 * y ^ 2) - 1]
    rw [hA, hB]
    funext i j 
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Fin.sum_univ_succ]
    <;> ring_nf
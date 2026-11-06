import Mathlib

open Real Set
open scoped BigOperators

/- 36. Prove the identity


$$

\sin \alpha+\sin 2 \alpha+\ldots+\sin n \alpha=\frac{\sin \frac{n+1}{2} \alpha}{\sin \frac{\alpha}{2}} \cdot \sin \frac{n x}{2}

$$
 -/
theorem algebra_189382 (α : ℝ) (n : ℕ) (h : sin (α / 2) ≠ 0) :
    ∑ k ∈ Finset.Icc 1 n, sin (k * α) =
    sin ((n + 1) * α / 2) / sin (α / 2) * sin (n * α / 2) := by
  -- mulitply by 2 and sin (α  / 2)
  rw [← mul_right_inj' (show (2 : ℝ) ≠ 0 by norm_num), Finset.mul_sum]
  field_simp
  rw [Finset.sum_mul]
  -- write the terms as subtractions of cos
  simp_rw [two_mul_sin_mul_sin]
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.succ_eq_add_one, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one]
  rw [← mul_assoc, two_mul_sin_mul_sin]
  -- simplify the expressions
  convert_to ∑ i ∈ Finset.range n, (cos ((i + 1) * α - α/2) - cos ((i + 2) * α - α/2)) = cos ((0 + 1) * α - α/2) - cos ((n + 1) * α - α/2)
  . congr
    ext x
    congr 2
    . ring
    . ring
  . congr 2
    . ring
    . ring
  -- the sum becomes telescoping and easily solved
  let f (i : ℕ) := cos ((i + 1) * α - α / 2)
  convert_to ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n
  . congr
    ext i
    simp [f]
    ring_nf
  . simp [f]
  exact Finset.sum_range_sub' f n
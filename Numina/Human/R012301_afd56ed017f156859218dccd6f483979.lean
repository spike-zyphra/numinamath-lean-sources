import Mathlib

open Real

/- Compute the value of

$$
\frac{\cos 30.5^{\circ}+\cos 31.5^{\circ}+\ldots+\cos 44.5^{\circ}}{\sin 30.5^{\circ}+\sin 31.5^{\circ}+\ldots+\sin 44.5^{\circ}}
$$ -/
theorem algebra_609826 :
    (∑ i ∈ Finset.range 15, (cos ((30.5 + i) * π / 180))) / (∑ i ∈ Finset.range 15, (sin ((30.5 + i) * π / 180))) = 2 - √2 - √3 + √6 := by
  calc (∑ i ∈ Finset.range 15, (cos ((30.5 + i) * π / 180))) / (∑ i ∈ Finset.range 15, (sin ((30.5 + i) * π / 180)))
    -- Multiply both numerator and denominator by 2 sin (π / 360)
    -- We must show that sin (π / 360) ≠ 0 here
    _ = 2 * sin (π / 360) * (∑ i ∈ Finset.range 15, (cos ((30.5 + i) * π / 180))) / (2 * sin (π / 360) * (∑ i ∈ Finset.range 15, (sin ((30.5 + i) * π / 180)))) := by
      refine (mul_div_mul_left _ _ (ne_of_gt ?_)).symm
      simp
      exact sin_pos_of_pos_of_lt_pi (by simp [pi_pos]) (by linarith [pi_pos])
    -- Move the 2 sin (π / 360) inside the sum
    _ = (∑ i ∈ Finset.range 15, (2 * sin (π / 360) * cos ((30.5 + i) * π / 180))) / ∑ i ∈ Finset.range 15, (2 * sin (π / 360) * sin ((30.5 + i) * π / 180)) := by rw [Finset.mul_sum, Finset.mul_sum]
    -- Use the product-to-sum identities
    _ = (∑ i ∈ Finset.range 15, (sin (π / 360 - (30.5 + i) * π / 180) + sin (π / 360 + (30.5 + i) * π / 180))) / (∑ i ∈ Finset.range 15, (cos (π / 360 - (30.5 + i) * π / 180) - cos (π / 360 + (30.5 + i) * π / 180))) := by simp [two_mul_sin_mul_cos, two_mul_sin_mul_sin]
    -- Simplify the arguments of the sine and cosine functions
    _ = (∑ i ∈ Finset.range 15, (sin (-((30 + i) * π / 180)) + sin ((30 + (i + 1)) * π / 180))) / (∑ i ∈ Finset.range 15, (cos (-((30 + i) * π / 180)) - cos ((30 + (i + 1)) * π / 180))) := by
      congrm (∑ i ∈ Finset.range 15, (sin ?_ + sin ?_)) / (∑ i ∈ Finset.range 15, (cos ?_ - cos ?_)) <;> linarith
    -- Write it as the sum of f(i+1) - f(i)
    _ = (∑ i ∈ Finset.range 15, (sin ((30 + (i + 1 : ℕ)) * π / 180) - sin ((30 + i) * π / 180))) / (∑ i ∈ Finset.range 15, (-cos ((30 + (i + 1 : ℕ)) * π / 180) - -cos ((30 + i) * π / 180))) := by
      congrm (∑ i ∈ Finset.range 15, ?_) / (∑ i ∈ Finset.range 15, ?_)
      . simp [sin_neg]
        ring
      . simp [cos_neg]
        ring
    -- We use the fact that ∑ i ∈ range n, (f (i + 1) - f i) = f n - f 0
    _ = (sin ((30 + 15) * π / 180) - sin (30 * π / 180)) / (-cos ((30 + 15) * π / 180) - -cos (30 * π / 180)) := by
      rw [Finset.sum_range_sub (f := fun (i : ℕ) => sin ((30 + i) * π / 180)), Finset.sum_range_sub (f := fun (i : ℕ) => -cos ((30 + i) * π / 180))]
      simp
    -- Simplify the arguments of the sine and cosine functions
    _ = (sin (π / 4) - sin (π / 6)) / (-cos (π / 4) - -cos (π / 6)) := by
      congrm (sin ?_ - sin ?_) / (-cos ?_ - -cos ?_) <;> ring
    -- Simplify the final expression
    _ = 2 - √2 - √3 + √6 := by
      simp
      -- We must show that (-(√2 / 2) + √3 / 2) ≠ 0
      have h₀ : (-(√2 / 2) + √3 / 2) ≠ 0 := by
        intro h₀
        have h₀ : √2 = √3 := by linarith
        apply_fun (· ^ 2) at h₀
        simp at h₀
      -- Eliminate the denominatorz
      rw [div_eq_iff h₀, show √6 = √2 * √3 by rw [← sqrt_mul (by simp)]; norm_num]
      ring_nf
      simp
      ring

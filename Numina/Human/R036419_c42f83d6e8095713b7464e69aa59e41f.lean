import Mathlib
set_option maxHeartbeats 5000000
open Real Set
open scoped BigOperators

/- 10. Given $\theta_{1}, \theta_{2}, \cdots, \theta_{n} \in\left(0, \frac{\pi}{2}\right)$, let

$$

M=\left(\sum_{i=1}^{n} \tan \theta_{i}\right)\left(\sum_{i=1}^{n} \cot \theta_{i}\right), N=\left(\sum_{i=1}^{n} \sin \theta_{i}\right)\left(\sum_{i=1}^{n} \csc \theta_{i}\right) \text {. }

$$


Then the size relationship between $M$ and $N$ is $\qquad$ . -/
theorem algebra_135614 {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ)
  (hθ : ∀ i, θ i ∈ Ioo 0 (π/2)) :
  (∑ i, tan (θ i)) * (∑ i, cot (θ i)) ≥
  (∑ i, sin (θ i)) * (∑ i, 1/sin (θ i)) := by
  simp at hθ
  -- for formalization, we'll often need sin >0 cos > 0
  have h0: ∀ i, 0 < sin (θ i) := by
    intro i
    apply sin_pos_of_mem_Ioo; simp
    constructor
    linarith [hθ i]
    linarith [hθ i]
  have h1: ∀ i, 0 < cos (θ i) := by
    intro i
    apply cos_pos_of_mem_Ioo; simp
    constructor
    linarith [hθ i]
    linarith [hθ i]

  --for start, compare with 0
  suffices 0 ≤ 2*(∑ i : Fin n, tan (θ i)) * ∑ i : Fin n, cot (θ i) - 2*(∑ i : Fin n, sin (θ i)) * ∑ i : Fin n, 1 / sin (θ i) by linarith
  -- smart rearrangement
  conv_rhs =>
    calc _
    _ = ( ∑ i : Fin n, tan (θ i)) * ∑ i : Fin n, (θ i).cot + ( ∑ i : Fin n, tan (θ i)) * ∑ i : Fin n, (θ i).cot - ( ∑ i : Fin n, sin (θ i)) * ∑ i : Fin n, 1 / sin (θ i) - ( ∑ i : Fin n, sin (θ i)) * ∑ i : Fin n, 1 / sin (θ i) := by ring_nf; simp
    _ = ( ∑ i : Fin n, (θ i).cot) * ∑ i : Fin n, (θ i).tan + ( ∑ i : Fin n, tan (θ i)) * ∑ i : Fin n, (θ i).cot - ( ∑ i : Fin n, 1 / sin (θ i)) * ∑ i : Fin n, sin (θ i) - ( ∑ i : Fin n, sin (θ i)) * ∑ i : Fin n, 1 / sin (θ i) := by simp; rw [mul_comm]; simp; rw [mul_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, ((θ i).cot * tan (θ j) + tan (θ i) * (θ j).cot - 1 / sin (θ i) * sin (θ j) - sin (θ i) * (1 / sin (θ j))) := by
      conv_lhs =>
        rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        rhs; intro i
        rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  -- suffices to show each of the terms is nonnegative
  apply Finset.sum_nonneg
  intro i _hi;
  apply Finset.sum_nonneg
  intro j _hj
  -- let's get rid of the denominator
  apply (mul_le_mul_right (a:=sin (θ j) * sin (θ i)) (by nlinarith [h0 j, h0 i])).mp
  rw [zero_mul]
  conv_rhs =>
    calc _
    _ = (cot (θ i) * tan (θ j) + tan (θ i) * cot (θ j) - sin (θ j) / sin (θ i) - sin (θ i) / sin (θ j)) * (sin (θ j) * sin (θ i)) := by ring_nf
    _ = cot (θ i) * tan (θ j) * sin (θ j) * sin (θ i) + tan (θ i) * cot (θ j) * sin (θ j) * sin (θ i) - sin (θ j) * sin (θ j) * (sin (θ i) / sin (θ i)) - sin (θ i) * (sin (θ j)/ sin (θ j)) * sin (θ i)  := by ring_nf
    _ = (cos (θ i) / sin (θ i)) * tan (θ j) * sin (θ j) * sin (θ i) + tan (θ i) * (cos (θ j)/sin (θ j)) * sin (θ j) * sin (θ i) - sin (θ j) * sin (θ j) - sin (θ i) * sin (θ i)  := by rw [div_self (by nlinarith [h0 j, h0 i]), div_self (by nlinarith [h0 j, h0 i]), mul_one, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]; ring_nf;
    _ = cos (θ i) * (sin (θ i)  / sin (θ i)) * tan (θ j) * sin (θ j) + tan (θ i) * (sin (θ j)/sin (θ j)) * cos (θ j) * sin (θ i) - sin (θ j) * sin (θ j) - sin (θ i) * sin (θ i)  := by ring_nf;
    _ = cos (θ i) * tan (θ j) * sin (θ j) + tan (θ i) * cos (θ j) * sin (θ i) - sin (θ j) * sin (θ j) - sin (θ i) * sin (θ i)  := by rw [div_self (by nlinarith [h0 j, h0 i]), div_self (by nlinarith [h0 j, h0 i]), mul_one, mul_one];

  -- also get rid of tangent
  apply (mul_le_mul_right (a:=cos (θ j) * cos (θ i)) (by nlinarith [h1 j, h1 i])).mp
  rw [zero_mul]
  conv_rhs =>
    calc _
    _ = (cos (θ i) * (sin (θ j) / cos (θ j)) * sin (θ j) + (sin (θ i)/cos (θ i)) * cos (θ j) * sin (θ i) - sin (θ j) * sin (θ j) - sin (θ i) * sin (θ i)) * (cos (θ j) * cos (θ i)) := by rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
    _ = cos (θ i) * (cos (θ j) / cos (θ j)) * sin (θ j) * sin (θ j) * cos (θ i) + (cos (θ i)/cos (θ i)) * cos (θ j) * sin (θ i) * cos (θ j) * sin (θ i) - sin (θ j) * sin (θ j) * cos (θ j) * cos (θ i) - sin (θ i) * sin (θ i) * cos (θ j) * cos (θ i) := by ring_nf
    _ = cos (θ i)^2 * sin (θ j)^2 + cos (θ j)^2 * sin (θ i)^2 - sin (θ j)^2 * cos (θ i) * cos (θ j) - sin (θ i)^2 * cos (θ i) * cos (θ j) := by rw [div_self (by nlinarith [h1 j]), div_self (by nlinarith [h1 i]), one_mul, mul_one]; ring_nf
    _ = (cos (θ i) - cos (θ j)) * (sin (θ j)^2 * cos (θ i) - sin (θ i)^2 * cos (θ j)) := by ring_nf
  -- now we can split by trichotomy on θ i and θ j
  cases' lt_trichotomy (θ i) (θ j) with hij hij
  · apply mul_nonneg
    simp
    apply cos_le_cos_of_nonneg_of_le_pi
    linarith [hθ i]
    linarith [hθ j]
    linarith
    simp
    apply mul_le_mul
    apply pow_le_pow_left₀
    apply sin_nonneg_of_mem_Icc
    simp
    constructor
    linarith [hθ i]
    linarith [hθ i]
    apply sin_le_sin_of_le_of_le_pi_div_two
    linarith [hθ i]
    linarith [hθ j]
    linarith
    apply cos_le_cos_of_nonneg_of_le_pi
    linarith [hθ i]
    linarith [hθ j]
    linarith
    apply cos_nonneg_of_mem_Icc
    simp
    constructor
    linarith [hθ j]
    linarith [hθ j]
    apply sq_nonneg
  cases' hij with hij hij
  · -- we just show that the first term is zero
    suffices 0 = cos (θ i) - cos (θ j) by
      rw [← this]; simp
    rw [hij]; simp
  · conv_rhs =>
      calc _
      _ = (cos (θ j) - cos (θ i)) * (sin (θ i) ^ 2 * cos (θ j) - sin (θ j) ^ 2 * cos (θ i)) := by ring_nf
    apply mul_nonneg
    simp
    apply cos_le_cos_of_nonneg_of_le_pi
    linarith [hθ j];
    linarith [hθ i]
    linarith
    simp
    apply mul_le_mul
    apply pow_le_pow_left₀
    apply sin_nonneg_of_mem_Icc
    simp
    constructor
    linarith [hθ j]
    linarith [hθ j]
    apply sin_le_sin_of_le_of_le_pi_div_two
    linarith [hθ j]
    linarith [hθ i]
    linarith
    apply cos_le_cos_of_nonneg_of_le_pi
    linarith [hθ j]
    linarith [hθ i]
    linarith
    apply cos_nonneg_of_mem_Icc
    simp
    constructor
    linarith [hθ i]
    linarith [hθ i]
    apply sq_nonneg
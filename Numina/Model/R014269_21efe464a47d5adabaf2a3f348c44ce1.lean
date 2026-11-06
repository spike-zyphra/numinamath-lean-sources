import Mathlib

open Real Set

theorem inequalities_289322 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ Real.pi) (hy : 0 ≤ y ∧ y ≤ Real.pi) (hz : 0 ≤ z ∧ z ≤ Real.pi) :
    sin x + sin y + sin z ≥ sin (x + y + z) := by
  have h1 : 0 ≤ x := hx.1
  have h2 : 0 ≤ y := hy.1
  have h3 : 0 ≤ z := hz.1
  have h4 : x ≤ Real.pi := hx.2
  have h5 : y ≤ Real.pi := hy.2
  have h6 : z ≤ Real.pi := hz.2
  have hsin1 : 0 ≤ sin x := by
    apply sin_nonneg_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_gt_three, h1, h4]
  have hsin2 : 0 ≤ sin y := by
    apply sin_nonneg_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_gt_three, h2, h5]
  have hsin3 : 0 ≤ sin z := by
    apply sin_nonneg_of_nonneg_of_le_pi
    all_goals linarith [Real.pi_gt_three, h3, h6]
  have h7 : sin (x + y + z) = sin x * cos y * cos z + sin y * cos x * cos z + sin z * cos x * cos y - sin x * sin y * sin z := by
    simp [sin_add, cos_add, sin_add, cos_add, mul_add, mul_assoc]
    <;> ring_nf
    <;> simp [mul_assoc, mul_add]
    <;> ring
  rw [h7]
  have hcos1 : -1 ≤ cos x := by
    have h : -1 ≤ cos x := by
      linarith [Real.neg_one_le_cos x, Real.cos_le_one x]
    linarith
  have hcos2 : cos x ≤ 1 := by
    apply Real.cos_le_one
  have hcos3 : -1 ≤ cos y := by
    have h : -1 ≤ cos y := by
      linarith [Real.neg_one_le_cos y, Real.cos_le_one y]
    linarith
  have hcos4 : cos y ≤ 1 := by
    apply Real.cos_le_one
  have hcos5 : -1 ≤ cos z := by
    have h : -1 ≤ cos z := by
      linarith [Real.neg_one_le_cos z, Real.cos_le_one z]
    linarith
  have hcos6 : cos z ≤ 1 := by
    apply Real.cos_le_one
  have h8 : 0 ≤ sin x * sin y := by
    nlinarith
  have h9 : 0 ≤ sin y * sin z := by
    nlinarith
  have h10 : 0 ≤ sin x * sin z := by
    nlinarith
  have h11 : sin x * sin y * sin z ≥ 0 := by
    apply mul_nonneg
    apply mul_nonneg
    all_goals nlinarith
  have h12 : sin x * cos y * cos z ≤ sin x := by
    nlinarith [sq_nonneg (cos y), sq_nonneg (cos z - 1), sq_nonneg (cos y - 1), sq_nonneg (cos z - cos y), Real.cos_le_one y, Real.cos_le_one z, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z]
  have h13 : sin y * cos x * cos z ≤ sin y := by
    nlinarith [sq_nonneg (cos x), sq_nonneg (cos z - 1), sq_nonneg (cos x - 1), sq_nonneg (cos z - cos x), Real.cos_le_one x, Real.cos_le_one z, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq z]
  have h14 : sin z * cos x * cos y ≤ sin z := by
    nlinarith [sq_nonneg (cos x), sq_nonneg (cos y - 1), sq_nonneg (cos x - 1), sq_nonneg (cos y - cos x), Real.cos_le_one x, Real.cos_le_one y, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y]
  have h15 : sin x * cos y * cos z ≥ -sin x := by
    nlinarith [sq_nonneg (cos y + 1), sq_nonneg (cos z + 1), sq_nonneg (cos y + cos z), Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z, Real.sin_sq_add_cos_sq x]
  have h16 : sin y * cos x * cos z ≥ -sin y := by
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos z + 1), sq_nonneg (cos x + cos z), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq z, Real.sin_sq_add_cos_sq y]
  have h17 : sin z * cos x * cos y ≥ -sin z := by
    nlinarith [sq_nonneg (cos x + 1), sq_nonneg (cos y + 1), sq_nonneg (cos x + cos y), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z]
  nlinarith [hsin1, hsin2, hsin3, hcos1, hcos2, hcos3, hcos4, hcos5, hcos6,
          Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq y, Real.sin_sq_add_cos_sq z,
          mul_nonneg hsin1 hsin2, mul_nonneg hsin2 hsin3, mul_nonneg hsin1 hsin3]
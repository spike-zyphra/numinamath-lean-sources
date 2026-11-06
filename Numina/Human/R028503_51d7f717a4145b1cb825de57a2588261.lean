import Mathlib

open Real Set

/-Find the maximum of \[\sqrt{x + 27} + \sqrt{13 - x} + \sqrt{x}\]for $0 \le x \le 13.$-/
theorem algebra_11570 (f : ℝ → ℝ) (hf : f = fun x => sqrt (x + 27) + sqrt (13 - x) + sqrt x) :
    IsGreatest {y | ∃x : ℝ, 0 ≤ x ∧ x ≤ 13 ∧ y = f x} 11 := by
  constructor
  . -- Equality occurs when $x = 9,$ so the maximum value is $\boxed{11}.$
    rw [hf]
    use 9
    simp
    use (by norm_num)
    have : (9 + 27 : ℝ) = 6^2 := by norm_num
    rw [this, sqrt_sq (by norm_num)]
    have : (13 - 9 : ℝ) = 2^2 := by norm_num
    rw [this, sqrt_sq (by norm_num)]
    have : (9 : ℝ) = 3^2 := by norm_num
    rw [this, sqrt_sq (by norm_num)]
    norm_num
  · apply mem_upperBounds.mpr
    simp
    intro y x hx₁ hx₂ hy
    rw [hy]

    -- By Cauchy-Schwarz applied to $ \left( 1,\frac{1}{3},\frac{1}{2}\right) $ and $ (\sqrt{x+27},\sqrt{13-x},\sqrt{x}) $, \[\left( 1 + \frac{1}{3} + \frac{1}{2} \right) ((x + 27) + 3(13 - x) + 2x) \ge (\sqrt{x + 27} + \sqrt{13 - x} + \sqrt{x})^2.\]
    have ineq1 : (sqrt (x + 27) + sqrt (13 - x) + sqrt x)^2 ≤ (1 + 1/3 + 1/2) * ((x+27) + 3*(13 - x) + 2*x) := by
      -- in order to use Finset.expect_mul_sq_le_sq_mul_sq, we need to define some variables
      have : ∃S : Finset ℕ, S = {0, 1, 2} := by simp
      rcases this with ⟨S, hS⟩
      have : ∃a : ℕ → ℝ, a =
          fun n => match n with
          | 0 => √1
          | 1 => √(1/3)
          | 2 => √(1/2)
          | _ => 0
        := by simp
      rcases this with ⟨a, ha⟩
      have : ∃b : ℕ → ℝ, b = fun n => match n with
          | 0 => √1 * √(x + 27)
          | 1 => √3 * √(13 - x)
          | 2 => √2 * √x
          | _ => 0
        := by simp
      rcases this with ⟨b, hb⟩
      have : (∑ i ∈ S, a i * b i) = (sqrt (x + 27) + sqrt (13 - x) + sqrt x) := by
        simp [hS, ha, hb, add_assoc]
      rw [this.symm]
      have : (1 + 1 / 3 + 1 / 2) = (∑ i ∈ S, a i ^ 2) := by
        simp [hS, ha, hb]
        ring_nf
      rw [this]
      have : ((x+27) + 3*(13 - x) + 2*x) = (∑ i ∈ S, b i ^ 2) := by
        simp [hS, ha, hb]
        ring_nf
        repeat rw [Real.sq_sqrt (by linarith)]
        ring_nf
      rw [this]
      ring_nf
      simp
      apply Finset.sum_mul_sq_le_sq_mul_sq

    have : (1 + 1/3 + 1/2) * ((x+27) + 3*(13 - x) + 2*x) = 11^2 := by
      linarith
    rw [this] at ineq1
    -- Hence, \[(\sqrt{x + 27} + \sqrt{13 - x} + \sqrt{x})^2 \le 121,\]so $\sqrt{x + 27} + \sqrt{13 - x} + \sqrt{x} \le 11.$
    have ineq2 : sqrt (x + 27) + sqrt (13 - x) + sqrt x ≤ 11 := by
      have : 0 < (2 : ℝ) := by norm_num
      apply (rpow_le_rpow_iff ?hx ?hy this).mp
      norm_cast
      norm_cast at ineq1
      repeat positivity

    rw [hf]
    simp
    exact ineq2

import Mathlib

open Finset Real Complex Polynomial

/- suppose ω is 11-th primitive root,
then x^11-1 = ∏_{i=0}^{10}(x-ω^i) . -/
lemma aux_4077 (ω : ℂ) (h : IsPrimitiveRoot ω 11) : X ^ 11 - C 1 = ∏ i ∈ range 11, (X - C (ω ^ i)) := by
  rw [X_pow_sub_C_eq_prod h (by decide : 0 < 11) (by norm_num : 1 ^ 11 = (1 : ℂ))]
  apply prod_congr rfl
  intros; rw [mul_one]

/- Evaluate $(2-w)(2-w^2)\cdots(2-w^{10})$ where $w=e^{2\pi i/11}.$-/
theorem precalculus_4077 {ω : ℂ} (hωval : ω = exp (2 * π * I / 11)) : ∏ i ∈ range 10, (2 - ω ^ (i + 1)) = 2047 := by
  -- ω=e^{2πi/11} is 11-th primitive root
  have hω : IsPrimitiveRoot ω 11 := by
    rw [Complex.isPrimitiveRoot_iff ω 11 (by norm_num)]
    use 1
    constructor
    . norm_num
    use (by simp)
    norm_cast
    rw [hωval, mul_assoc, ← mul_div_assoc, mul_one, mul_div_assoc]
    push_cast
    rfl
  -- ∏_{i=0}^{9}(2-ω^(i+1)) = ∏_{i=0}^{10}(2-ω^i)
  have : ∏ i ∈ range 10, (2 - ω ^ (i + 1)) = ∏ i ∈ range 11, (2 - ω ^ i ) := by
    rw [eq_comm, show 11 = 10 + 1 by decide, prod_range_succ']
    rw [pow_zero, show 2 - 1 = (1 : ℂ) by norm_num, mul_one]
  rw [this]
  -- ∏_{i=0}^{10}(2-ω^i) = P(ω), where P(x)=x^11-1
  have : ∏ i ∈ range 11, (2 - ω ^ i) = (∏ i ∈ range 11, (X - C (ω ^ i))).eval 2 := by
    simp [prod_range_succ]
  rw [this, ← aux_4077 ω hω]
  simp; norm_num

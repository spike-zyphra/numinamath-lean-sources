import Mathlib

open Real Set
open scoped Real

/- Compute the number of degrees in the smallest positive angle $x$ such that
\[8 \sin x \cos^5 x - 8 \sin^5 x \cos x = 1.\] -/
theorem calculus_13255 :
  IsLeast {x : ℝ | 0 < x ∧ 8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x = 1} (7.5 * π / 180) := by
  have hi:∀(x:ℝ), 8 * sin x * cos x ^ 5 - 8 * sin x ^ 5 * cos x = 2 * sin (4*x) := by -- First, prove the identity
    intro x
    calc
    _ = 4*(2*sin x*cos x)*(cos x^4-sin x^4) := by nlinarith
    _ = 4*sin (2*x)*(cos x^4-sin x^4) := by rw [sin_two_mul]
    _ = 4*sin (2*x)*(cos x^2+sin x^2)*(cos x^2-sin x^2) := by nlinarith
    _ = 4*sin (2*x)*1*cos (2*x) := by rw [cos_sq_add_sin_sq,cos_two_mul']
    _ = 2*(2*sin (2*x)*cos (2*x)) := by nlinarith
    _ = 2*sin (2*(2*x)) := by rw [sin_two_mul (2*x)]
    _ = 2*sin (4*x) := by rw [show 2*(2*x)=4*x by linarith]
  unfold IsLeast
  constructor
  -- 7.5 ° satisfies the condition
  simp
  constructor
  -- To prove 0 < 7.5 * π
  norm_num
  exact pi_pos
  -- To prove 7.5 ° satisfies the equation
  rw [hi (7.5 * π / 180),show 4 * (7.5 * π / 180) = π/6 by linarith]
  rw [sin_pi_div_six]
  simp
  -- To prove 7.5 ° is the minimum
  unfold lowerBounds
  simp
  intro y hy1 hy2
  rw [hi y] at hy2
  have : sin (4*y) = sin (π/6) := by
    rw [sin_pi_div_six]
    linarith
  have := sin_eq_sin_iff.1 this -- Hence obtained the necessary and sufficient conditions for y : ∃ k, π / 6 = 2 * ↑k * π + 4 * y ∨ π / 6 = (2 * ↑k + 1) * π - 4 * y
  have : ¬(7.5 * π / 180 > y) := by -- Using the method of proof by contradiction
    rw [show 7.5 * π / 180 = π / 24 by ring]
    intro hf -- hf is the root of contradictions
    match this with
    |⟨k,hyy⟩ =>
    match hyy with
    | Or.inl hy3 => -- π / 6 = 2 * ↑k * π + 4 * y
      have hy3 : y = π/24-k*π/2 := by linarith
      rw [hy3] at hf
      have hf : 0 < (↑k:ℝ) := by nlinarith
      rw [hy3] at hy1
      have hy1 : (↑k:ℝ)<1/12 := by nlinarith
      have hy1 := Int.add_one_le_ceil_iff.2 hy1
      rw [show ⌈(1:ℝ)/12⌉ = 1 by norm_num] at hy1
      have hy1: k ≤ 0 := by linarith
      have hy1: (↑k:ℝ) ≤ ↑(0:ℤ) := Int.cast_le.2 hy1
      have := lt_of_lt_of_le hf hy1
      simp at this
    | Or.inr hy4 => -- π / 6 = (2 * ↑k + 1) * π - 4 * y
      have hy4 : y = 5*π/24+k*π/2 := by linarith
      rw [hy4] at hf
      have hf : (↑k:ℝ) < -1/3 := by nlinarith
      rw [hy4] at hy1
      have hy1 :-5/12<(↑k:ℝ) := by nlinarith
      have hf := Int.add_one_le_ceil_iff.2 hf
      rw [show ⌈-(1:ℝ)/3⌉=0 by norm_num] at hf
      have hf : k ≤ -1 := by linarith
      have hf : (↑k:ℝ)≤(↑(-1:ℤ):ℝ) := Int.cast_le.2 hf
      have := lt_of_lt_of_le hy1 hf
      linarith
  simp at this
  exact this

import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- 1. Let the complex number $z$ satisfy $|z|=1$. Then the maximum value of $\left|z^{3}+3 z+2 \mathrm{i}\right|$ is ( ).
(A) $4 \sqrt{2}$
(B) $3 \sqrt{3}$
(C) $2 \sqrt{5}$
(D) $4 \sqrt{3}$ -/
theorem algebra_175567 :
  IsGreatest {x | ∃ z : ℂ, ‖z‖ = 1 ∧ x = ‖z^3 + 3 * z + 2 * .I‖} (3 * Real.sqrt 3) := by
  -- let z = a+b*i
  unfold IsGreatest upperBounds; simp
  constructor
  · -- we first need to show that the value is reachable, using a clever guess, boring sausage otherwise
    use Real.sqrt 3 / 2 + Complex.I/2
    unfold Complex.abs; simp; unfold normSq; simp; rw [div_mul_div_comm, show √3 *√3=3 by norm_num]; norm_num
    ring_nf; simp; rw [show Complex.I^3=Complex.I^2*I by ring_nf]; simp;
    conv_rhs =>
      rhs
      calc _
      _ = 49 / 4 + √3 * (-(√3 * (3 / 8)) + -((Complex.im (√3 ^ 2)) * (3 / 8)) + (Complex.re (√3 ^ 3)) * 8⁻¹) * 3 + 3 * (9 / 4) + (-(√3 * (3 / 8)) + -((Complex.im (√3 ^ 2)) * (3 / 8)) + (Complex.re (√3 ^ 3)) * 8⁻¹) ^ 2 + ((Complex.re (√3 ^ 2)) * (3 / 8) + (Complex.im (√3 ^ 3)) * 8⁻¹ + -8⁻¹) * 7 + ((Complex.re (√3 ^ 2)) * (3 / 8) + (Complex.im (√3 ^ 3)) * 8⁻¹ + -8⁻¹) ^ 2 := by ring_nf
      _ = 76 / 4 + √3*3/8 * (-√3 * 3 -((Complex.im (√3 ^ 2)) * 3) + Complex.re (√3 ^ 3)) + ((-√3 * 3 -(Complex.im (√3 ^ 2)) * 3 + (Complex.re (√3 ^ 3)))/8) ^ 2 + ((Complex.re (√3 ^ 2)) * 3 + (Complex.im (√3 ^ 3)) - 1) * 7/8 + (((Complex.re (√3 ^ 2)) * 3 + (Complex.im (√3 ^ 3)) - 1)/8) ^ 2 := by ring_nf
      _ = 76 / 4 + √3*3/8 * (-√3 * 3 + √3 ^ 3) + ((-√3 * 3 + (√3 ^ 3))/8) ^ 2 + (√3 ^ 2 * 3 - 1) * 7/8 + ((√3 ^ 2 * 3 - 1)/8) ^ 2 := by norm_cast; simp
      _ = 76 / 4 + √3*3/8 * (-√3 * 3 + √3 * 3) + ((-√3 * 3 + (√3 * 3))/8) ^ 2 + (3 * 3 - 1) * 7/8 + ((3 * 3 - 1)/8) ^ 2 := by rw [show √3 ^ 3 = √3 * √3^2 by ring_nf, Real.sq_sqrt (by norm_num)]
    norm_num
    rw [show (27:ℝ) = 3*3^2 by norm_num, Real.sqrt_mul, Real.sqrt_sq (by norm_num)]; norm_num
  · intro a z hz hz'
    rw [hz']; clear hz' a
    -- now we can start solving the core of the problem
    -- let z = a+b*i
    let q: (∃ a b:ℝ, z = a + b * I ∧ a = z.re ∧ b = z.im) := by
      use z.re
      use z.im
      simp
    obtain ⟨a, b, ⟨habz, adef, bdef⟩⟩ := q
    -- hz then gives that a^2+b^2=1
    unfold Complex.abs at hz; simp at hz; unfold normSq at hz; simp at hz; rw [← adef, ← bdef] at hz; ring_nf at hz
    -- we can also calculate z ^ 3 + 3 * z + 2 * I in terms of a and b
    have h2:=
      calc z ^ 3 + 3 * z + 2 * I
      _ = (a+b*I)^3 + 3 * (a+b*I) + 2 * I := by rw [habz]
      _ = (a^3 + 3 * a^2 * b * I - 3 * a*b^2 - b^3*I) + 3 * a + 3*b*I + 2*I := by ring_nf; rw [show Complex.I^3=Complex.I*(Complex.I^2) by ring_nf]; simp; ring_nf
      _ = a ^ 3 + 3 * a * (1-b^2) + (3 * a^2 * b - b^3 + 3 * b + 2)*I := by ring_nf
      _ = 4*a^3 + (3*(1-b^2)*b -b^3 + 3*b + 2)*I := by rw [show 1-(b:ℂ)^2=a^2 by norm_cast; linarith]; ring_nf
      _ = (4*a^3:ℝ) + ((-4*b^3 + 6*b + 2):ℝ)*I := by rify; ring_nf
    -- let's copmute the norm in terms of a, b
    rw [h2, abs_add_mul_I]
    refine (sqrt_le_left ?_).mpr ?_
    positivity
    ring_nf; rw [show a^6=(a^2)^3 by ring_nf, show a^2=1-b^2 by linarith, Real.sq_sqrt (by norm_num)]; ring_nf
    -- move to one side, factor and finish
    suffices 0 ≤ 7 - 24*b +12 *b ^ 2 + 16* b ^ 3 by linarith
    rw [show 7-24*b+12*b^2+16*b^3=(2*b-1)^2*(4*b+7) by ring_nf]
    apply mul_nonneg_iff.mpr
    left
    constructor
    <;> nlinarith
import Mathlib

/- Exercise 4. Find all real numbers $x$ and $y$ such that


$$

\left(x-\sqrt{x^{2}+1}\right)\left(y-\sqrt{y^{2}+1}\right)=1 \text { and }\left(x^{2}+y+2\right)\left(y^{2}+x+2\right)=8

$$
 -/
theorem algebra_291119 {x y : ℝ} (hx : (x - Real.sqrt (x ^ 2 + 1)) * (y - Real.sqrt (y ^ 2 + 1)) = 1)
    (hy : (x ^ 2 + y + 2) * (y ^ 2 + x + 2) = 8) :
    (x, y) = (1, -1) ∨ (x, y) = (-1, 1) := by
  -- First equation can be modified by verifying (x-√(x^2+1))*(x+√(x^2+1))=-1
  have hx': (x - Real.sqrt (x ^ 2 + 1)) * (x + Real.sqrt (x ^ 2 + 1)) = -1 := by
    ring_nf; rw [Real.sq_sqrt (by nlinarith)]; ring_nf
  have hy': (y - Real.sqrt (y ^ 2 + 1)) * (y + Real.sqrt (y ^ 2 + 1)) = -1 := by
    ring_nf; rw [Real.sq_sqrt (by nlinarith)]; ring_nf
  -- substituting into first equation we obtain new equations
  have hxy1: x + √(x ^ 2 + 1) = √(y^2+1) - y := by
    apply congr_arg (fun t => t * (x + √(x ^ 2 + 1))⁻¹) at hx'
    rw [mul_assoc, mul_inv_cancel₀ (
      by
      apply ne_of_gt;
      suffices -x < √(x^2+1) by nlinarith;
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    ), mul_one] at hx'
    rw [hx', mul_assoc, mul_comm] at hx
    apply congr_arg (fun t => (x + √(x^2+1)) * t) at hx
    rw [← mul_assoc ((x + √(x ^ 2 + 1))), ← mul_assoc ((x + √(x ^ 2 + 1))), mul_inv_cancel₀ (
      by
      apply ne_of_gt;
      suffices -x < √(x^2+1) by nlinarith;
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    ), one_mul] at hx
    simp at hx; exact hx.symm
  have hxy2: √(x^2+1)-x = y + √(y^2+1) := by
    apply congr_arg (fun t => t * (y + √(y ^ 2 + 1))⁻¹ ) at hy'
    rw [mul_assoc, mul_inv_cancel₀ (
      by
      apply ne_of_gt;
      suffices -y < √(y^2+1) by nlinarith;
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    ), mul_one] at hy'
    rw [hy'] at hx
    apply congr_arg (fun t => t * (y + √(y^2+1))) at hx
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀ (
      by
      apply ne_of_gt;
      suffices -y < √(y^2+1) by nlinarith;
      apply Real.lt_sqrt_of_sq_lt
      nlinarith
    )] at hx
    simp at hx; exact hx
  -- we can subtract the two obtained equations
  have hsub: x + √(x ^ 2 + 1) - (√(x^2+1)-x) = (√(y^2+1)-y) - (y + √(y^2+1)) := by linarith
  ring_nf at hsub
  apply congr_arg (fun t => t*1/2) at hsub; ring_nf at hsub
  -- we get that x=-y. Substitute into hy and solve
  have hyx: y=-x := by linarith
  rw [hyx, show (x ^ 2 + -x + 2) * ((-x) ^ 2 + x + 2) = (x^2+2)^2-x^2 by ring_nf] at hy
  -- define z = x^2
  let q:∃ z:ℝ, z = x^2 := by
    simp only [exists_eq]
  obtain ⟨z, zdef⟩ := q
  rw [←zdef] at hy
  -- simple quadratic
  apply congr_arg (fun x => x-8) at hy
  ring_nf at hy
  have sol := (quadratic_eq_zero_iff (a:=(1:ℝ)) (b:=(3:ℝ)) (c:=(-4:ℝ)) (by norm_num) (s:=5) (by unfold discrim; norm_num) z).mp
  ring_nf at hy sol
  specialize sol hy
  -- we get two solutions, one is negative so invalid
  cases' sol with sol sol
  rotate_left
  · -- eliminate invalid solution
    nlinarith
  -- finish
  rw [sol] at zdef
  suffices x=1 ∨ x=-1 by
    cases' this with x1 x2
    · left
      simp
      refine And.intro x1 ?_
      linarith
    · right
      simp
      refine And.intro x2 ?_
      linarith
  exact sq_eq_one_iff.mp (id (Eq.symm zdef))
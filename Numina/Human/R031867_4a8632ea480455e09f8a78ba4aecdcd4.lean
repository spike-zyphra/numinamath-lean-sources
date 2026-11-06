import Mathlib

/- Let $x,$ $y,$ $z$ be positive real numbers such that $x^2 + y^2 + z^2 = 1.$  Find the maximum value of
\[xy \sqrt{10} + yz.\] -/
theorem algebra_20292 :
  IsGreatest {u:ℝ | ∃(x y z:ℝ), u = x*y*√10+y*z ∧ x^2+y^2+z^2 = 1 ∧
  0 < x ∧ 0 < y ∧ 0 < z}
  (√11/2) := by
  -- when x^2+y^2+z^2=1, we can divide it into several
  -- expressions and use AM-GM.
  -- x^2+y^2+z^2 = (x^2+ky^2)+((1-k)y^2+z^2).
  --use AM-GM, we have factors xy and yz.
  have h1{k:ℝ}(x y z:ℝ)
    (hk1: 0 ≤ k)(hk2: k ≤ 1):
    2*x*y*√k + 2*y*z*√(1-k) ≤ x^2+y^2+z^2 := by
    have h1: x^2+y^2+z^2 = (x^2+k*y^2)+((1-k)*y^2+z^2) := by ring
    have h2: x^2+k*y^2 ≥ 2*x*y*√k := by
      have hh1: 2*x*y*√k = 2*x*(√k*y) := by ring
      have hh2 := two_mul_le_add_pow_two x (√k*y)
      have hh3: x^2+k*y^2 = x^2 + (√k*y)^2 := by
        have: k = √k^2 := by
          symm; exact Real.sq_sqrt hk1
        ring_nf
        nth_rw 1 [this]; simp; ring
      rw [hh1, hh3]
      exact hh2
    have h3: (1-k)*y^2+z^2 ≥ 2*y*z*√(1-k) := by
      have hh1: (1-k)*y^2+z^2 = (√(1-k)*y)^2 + z^2 := by
        have: 1-k = √(1-k)^2 := by
          symm; exact Real.sq_sqrt (sub_nonneg.mpr hk2)
        nth_rw 1 [this]; ring
      have hh2: 2*y*z*√(1-k) = 2*(√(1-k)*y)*z := by ring
      rw [hh1, hh2]
      apply two_mul_le_add_pow_two
    rw [h1]
    linarith [h2, h3]
  --we should choose such k that
  -- produce √10xy and yz. so here we choose 10/11
  have h2(x y z: ℝ):
    x*y*√10+y*z ≤ √11/2 * (x^2+y^2+z^2) := by
    have hk1: 0 ≤ (10/11:ℝ) := by norm_num
    have hk2: (10/11:ℝ) ≤ 1 := by norm_num
    have hh1 := h1 x y z hk1 hk2
    have hh2: x*y*√10 + y*z = √11/2 *
      (2*x*y*√(10/11) + 2*y*z*√(1-10/11)) := by
      norm_num; field_simp; ring
    rw [hh2]
    apply mul_le_mul_of_nonneg_left hh1
    apply div_nonneg
    exact Real.sqrt_nonneg 11
    norm_num
  -- thus we can work out the problem. notice that a^2+b^2 = 2ab when a=b,
  -- so reach minimum when x=√ky, √(1-k)y=z, or x = √10/11y, √1/11 y = z.
  -- solve the equations with x^2+y^2+z^2=1, we get
  -- x = √(10/22), y = √(11/22), z = √(1/22)
  rw [IsGreatest, upperBounds]; simp; constructor
  · -- use above xyz values
    use √(10/22), √(11/22), √(1/22)
    field_simp
    ring_nf; simp; ring
  · intro u x y z hu hxyz _ _ _
    rw [hu]
    rw [← mul_one (√11/2), ← hxyz]
    apply h2 x y z
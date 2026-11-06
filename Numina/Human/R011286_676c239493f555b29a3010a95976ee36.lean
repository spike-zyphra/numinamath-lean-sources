import Mathlib

/- Let $x$, $y$, $z$ be non-negative real numbers, and $x+y+z=1$. Prove that: $0 \leqslant x y+y z+$ $z x-2 x y z \leqslant \frac{7}{27}$. -/
theorem inequalities_112432 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hsum : x + y + z = 1) :
    0 ≤ x * y + y * z + z * x - 2 * x * y * z ∧
    x * y + y * z + z * x - 2 * x * y * z ≤ 7 / 27 := by

  -- wlog x≥y≥z
  wlog hxy:x≥y
  · simp at hxy
    specialize this y x z hy hx hz (by linarith) (by linarith)
    constructor <;> linarith
  wlog hyz:y≥z
  · simp at hxy hyz
    cases' lt_or_ge x z with hxz hxz
    specialize this z x y (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith)
    constructor <;> linarith
    simp at hxz
    specialize this x z y (by assumption) (by assumption) (by assumption) (by linarith) (by linarith) (by linarith)
    constructor <;> linarith
  -- we can form an arithmetic sequence with x+y, 1/2, z since x+y+z = 2*(1/2) which is a classic condition
  -- The sequence is clearly decreasing
  let q:∃ d:ℝ, x+y = 1/2+d ∧ 1/2-d=z := by
    use 1/2-z
    constructor
    linarith
    linarith
  obtain ⟨d, ⟨dxy, dz⟩⟩ := q
  -- since x≥ y≥z, we have x+y≥2*z, we can bound d with that
  have hd: 1/6 ≤ d ∧ d ≤ 1/2 := by
    constructor
    · linarith
    · linarith
  -- now we can prove the first inequality
  constructor
  · calc x * y + y * z + z * x - 2 * x * y * z
    _ = (x+y)*z+x*y*(1-2*z) := by ring_nf
    _ = 1/4-d^2+2*d*x*y := by rw [dxy, show 1-2*z=2*d by linarith, ← dz]; ring_nf
    _ ≥ 0 := by simp; apply add_nonneg; rotate_left; apply mul_nonneg; apply mul_nonneg; linarith; assumption; assumption; simp; nlinarith
  -- second inequality takes a bit more work
  · calc x * y + y * z + z * x - 2 * x * y * z
    _ = (x+y)*z+x*y*(1-2*z) := by ring_nf
    _ = 1/4-d^2+2*d*x*y := by rw [dxy, show 1-2*z=2*d by linarith, ← dz]; ring_nf
    _ ≤ 1/4 - d^2+2*d*((x+y)/2)^2 := by
      gcongr 1 / 4 - d ^ 2 + ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      apply (mul_le_mul_left (by norm_num)).mpr
      apply (mul_le_mul_left (by linarith)).mpr
      -- this is just AM-GM squared
      nlinarith
    _ = 1/4 - d^2+1/2*d*(1/2+d)^2 := by rw [dxy]; ring_nf
    _ = 1/4 + 1/4 * 2*d*(1/2-d)^2 := by ring_nf
    _ ≤ 1/4 + 1/4 * ((2*d+(1/2-d)+(1/2-d))/3)^3 := by
      apply add_le_add_left
      rw [mul_assoc (1/4), mul_assoc (1/4)]
      apply (mul_le_mul_left (by norm_num)).mpr
      -- AM-GM cubed
      have q:= Real.geom_mean_le_arith_mean3_weighted (w₁:=1/3) (w₂:=1/3) (w₃:=1/3) (p₁:=2*d) (p₂:=1/2-d) (p₃:=1/2-d) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith) (by norm_num)
      apply (pow_le_pow_iff_left₀ (n:=3) (by rw [← Real.mul_rpow (by linarith) (by linarith), ← Real.mul_rpow (by apply mul_nonneg; linarith; linarith) (by linarith)];apply Real.rpow_nonneg;apply mul_nonneg; apply mul_nonneg; linarith; linarith; linarith) (by nlinarith) (by norm_num)).mpr at q
      rw [← Real.mul_rpow (by linarith) (by linarith), ← Real.mul_rpow (by apply mul_nonneg; linarith; linarith) (by linarith), show _^3=_^(3:ℝ) by norm_cast, ← Real.rpow_mul, show (1:ℝ)/3*3=1 by norm_num, Real.rpow_one] at q
      ring_nf at q ⊢; linarith
      apply mul_nonneg; apply mul_nonneg; linarith; linarith; linarith
    _ = 1/4 + 1/4 * (1/3)^3 := by ring_nf
    _ = 7/27 := by ring_nf
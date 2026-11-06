import Mathlib

/-
Prove that for all $x>0$,

$$
1+x^{2016} \geq \frac{(2 x)^{2015}}{(1+x)^{2014}}
$$
 -/
theorem inequalities_100150 (x : ℝ) (hx : 0 < x) :
    1 + x ^ 2016 ≥ (2 * x) ^ 2015 / (1 + x) ^ 2014 := by
  rw [show 2016 = 2014 + 2 from rfl]
  rw [show 2015 = 2014 + 1 from rfl]
  --set n := 2014
  rw [show 2014 = 2 * 1007 from rfl]
  generalize 1007 = n
  have den_pos : (1 + x) ^ (2 * n) > 0 := by
    have : 1 + x > 0 := by linarith
    --nlinarith
    exact pow_pos this (2 * n)
  /-
  We want to show that

  $$ \left(1+x^{2016}\right)(1+x)^{2014} \geq(2 x)^{2015} $$
  -/
  --field_simp [this]
  suffices (1 + x ^ (2 * n + 2)) * ((1 + x) ^ (2 * n)) ≥ (2 * x) ^ (2 * n + 1) by
    exact (div_le_iff₀ den_pos).mpr this
  /-
  To do this, let's apply the arithmetic-geometric mean inequality to each parenthesis on the left side. We get

  $$ 1+x^{2016} \geq 2 \sqrt{1 \times x^{2016}}=2 x^{1008} $$
  -/
  have h1 : 1 + x ^ (2 * n + 2) ≥ 2 * (x ^ (n + 1)) := by
    have := two_mul_le_add_sq 1 (x ^ (n + 1))
    simp
    convert this using 1
    . ring
    . ring
  /-
  and

  $$ (1+x)^{2014} \geq(2 \sqrt{x})^{2014}=2^{2014} x^{1007} $$

  Multiplying these two inequalities completes the proof.
   -/
  have h2 : (1 + x) ^ (2 * n) ≥ 2 ^ (2 * n) * x ^ n := by
    have sq_sqrt_2 : √x ^ 2 = x := by
        refine Real.sq_sqrt ?_
        linarith
    have := two_mul_le_add_of_sq_eq_mul (a := 1) (b := x) (r := √x)
      (by simp)
      (by linarith)
      (by
        simp
        exact sq_sqrt_2
      )
    have : (2 * √x) ^ (2 * n) ≤ (1 + x) ^ (2 * n) := by
      refine pow_le_pow_left₀ ?_ this (2 * n)
      simp
    simp
    convert this
    ring_nf
    rw [show √x ^ (n * 2) = (√x ^ 2) ^ n by ring]
    rw [sq_sqrt_2]
  set a := 1 + x ^ (2 * n + 2)
  set b := (1 + x) ^ (2 * n)
  set c := 2 * (x ^ (n + 1))
  set d := 2 ^ (2 * n) * x ^ n
  have : a * b ≥ c * d := by
    have : c ≥ 0 := by
      unfold c
      have : x ^ (n + 1) > 0 := by
        exact pow_pos hx (n + 1)
      nlinarith
    nlinarith
  --have := mul_le_mul' h1 h2
  unfold c d at this
  convert this
  ring

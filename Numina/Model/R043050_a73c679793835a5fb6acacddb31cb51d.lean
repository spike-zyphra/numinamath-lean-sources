import Mathlib

open Finset

theorem inequalities_23797 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c = a + b + c) :
    1 / (2 * a + b + c) ^ 2 + 1 / (2 * b + c + a) ^ 2 + 1 / (2 * c + a + b) ^ 2 ≤ 3 / 16 := by


  -- For positive real numbers x,y,z, by the AM-GM inequality, we obtain 1 / ((2 * x + y + z)^2) ≤ 1 / (4 * (x+y)*(x+z))
  have t (x y z : ℝ) (xpos : 0 < x) (ypos : 0 < y) (zpos : 0 < z) : 1 / ((2*x + y + z)^2) ≤ 1 / (4 * (x + y)*(x + z)) := by
    apply one_div_le_one_div_of_le
    positivity
    have l := two_mul_le_add_sq (x + y) (x + z)
    ring_nf at l
    ring_nf
    linarith

  have t1 := t a b c (by positivity) (by positivity) (by positivity)
  have t2 := t b c a (by positivity) (by positivity) (by positivity)
  have t3 := t c a b (by positivity) (by positivity) (by positivity)

  -- Applying this to the LHS of the inequality to prove, we have [LHS] ≤ (a + b + c) / (2 * (a + b) * (a + c) * (b + c))
  have h1 := calc
    1 / (2 * a + b + c) ^ 2 + 1 / (2 * b + c + a) ^ 2 + 1 / (2 * c + a + b) ^ 2 ≤ 1 / (4 * (a + b) * (a + c)) + 1 / (4 * (b + c) * (b + a)) + 1 / (4 * (c + a) * (c + b)) := add_le_add_three t1 t2 t3
    _ = (a + b + c) / (2 * (a + b) * (a + c) * (b + c)) := by
      field_simp
      ring

  clear t1 t2 t3

  -- Second application of AM-GM

  let w : Fin 6 → ℝ := fun _ => (1:ℝ)/6

  let f : Fin 6 → ℝ := fun i =>
    match i with
    | 0 => a^2 * b
    | 1 => a^2 * c
    | 2 => b^2 * a
    | 3 => b^2 * c
    | 4 => c^2 * a
    | 5 => c^2 * b

  have h2 := Real.geom_mean_le_arith_mean_weighted {0, 1, 2, 3, 4, 5} w f (by
    intro _ _
    positivity
  ) (by
    simp
    norm_num
  ) (by
    intro i _
    fin_cases i <;> positivity
  )

  simp at h2
  unfold w at h2
  unfold f at h2
  dsimp at h2
  norm_num at h2

  repeat rw [←Real.mul_rpow (by positivity) (by positivity)] at h2

  rw [
    show (a ^ 2 * b * (a ^ 2 * c * (b ^ 2 * a * (b ^ 2 * c * (c ^ 2 * a * (c ^ 2 * b)))))) = (a * b * c)^6 by ring
  ] at h2

  rw [show ((a*b*c) ^ 6) ^ ((1:ℝ) / 6) = (a*b*c) by
    rw [show (a*b*c) ^ 6 = ((a*b*c) ^ 2)^3 by ring]
    rw [show ((a*b*c) ^ 2)^3 = ((a*b*c) ^ (2:ℝ))^(3:ℝ) by norm_cast]
    repeat rw [←Real.rpow_mul (by positivity)]
    norm_num
  ] at h2

  -- Second application of AM-GM yields this
  have h3 : 6 * a * b * c ≤ a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b := by
    nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
      sq_nonneg (a^2 - b^2), sq_nonneg (a^2 - c^2), sq_nonneg (b^2 - c^2)]

  -- We need to show $\sum \frac{1}{(2a+b+c)^2} \leq \frac{3}{16}$.
  -- We have shown $\sum \frac{1}{(2a+b+c)^2} \leq \frac{a + b + c}{2(a + b)(a + c)(b + c)}$
  -- Now, we need $\frac{a + b + c}{2(a + b)(a + c)(b + c)} \leq \frac{3}{16}$

  have h4 : (a + b + c) / (2 * (a + b) * (a + c) * (b + c)) ≤ 3 / 16 := by

    -- First, derive from the hypothesis.
    have h' : a * b + a * c + b * c = a * b * c * (a + b + c) := by
      field_simp at h
      nlinarith

    -- We can now use algebraic manipulation to show that $(a + b + c) / (2(a + b)(a + c)(b + c)) \leq 3/16$
    have h4' : 16 * (a + b + c) ≤ 6 * (a + b) * (a + c) * (b + c) := by
      nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c),
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        h', mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith

  -- Finally, conclude the inequality
  linarith only [h1, h4]
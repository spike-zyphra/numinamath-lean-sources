import Mathlib


open Real Set
open scoped BigOperators

/- Example 2 Given that $x, y$ are both in the interval $(-2,2)$, and $x y=-1$, then what is the minimum value of the function $u=\frac{4}{4-x^{2}}+\frac{9}{9-y^{2}}$? -/
theorem algebra_189898 :
  IsLeast {u | ∃ x y : ℝ, x ∈ Ioo (-2) 2 ∧ y ∈ Ioo (-2) 2 ∧ x * y = -1 ∧ u = 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2)} (12 / 5) := by
  constructor
  -- Show that when x = 2 / 3 , we achieve u = 12/5.
  · simp
    use (√2 / √3)
    constructor
    constructor
    have aux1 : √ 2 / √ 3 > 0 := by positivity
    linarith
    refine (div_lt_iff₀  ?_).mpr ?_
    positivity
    refine (sqrt_lt ?_ ?_).mpr ?_
    linarith
    positivity
    rw [mul_pow]
    simp
    norm_num
    use (- (√3 / √2))
    constructor
    constructor
    have aux2 : √ 3 / √ 2 < 2  := by
      refine (div_lt_iff₀  ?_).mpr ?_
      positivity
      refine (sqrt_lt ?_ ?_).mpr ?_
      linarith
      positivity
      rw [mul_pow]
      simp
      norm_num
    linarith
    have aux3 : (- (√3 / √2)) < 0 := by 
      have aux1 : √ 3 / √ 2 > 0 := by positivity
      linarith
    linarith
    constructor
    simp
    field_simp
    norm_num
  -- Show that the above u ≥ 12/5.
  simp
  unfold lowerBounds
  simp
  intro u x hx1 hx2 y hy1 hy2 hxy hy
  have xsqneq : x ^ 2 ≠ 0 := by 
    have xneq : x ≠ 0 := by 
      by_contra hc
      rw [hc] at hxy
      simp at hxy
    exact pow_ne_zero 2 xneq
  have ysqneq : y ^ 2 ≠ 0 := by 
    have xneq : y ≠ 0 := by 
      by_contra hc
      rw [hc] at hxy
      simp at hxy
    exact pow_ne_zero 2 xneq
  have yeq : y ^ 2 = 1 / x ^ 2 := by 
    have xyeq' : x ^ 2 * y ^ 2 = 1 := by 
      calc 
        _ = (x * y ) ^ 2 := by 
          ring
        _ = 1 := by 
          rw [hxy]
          simp
    rw [←xyeq']
    field_simp
  have neq1 : 4 - x ^ 2 ≠ 0 := by 
    have xle : x ^ 2 < 4 := by 
      nlinarith
    by_contra hc
    linarith
  have neq2 : 9 - y ^ 2 ≠ 0 := by
    have xle : y ^ 2 < 9 := by 
      nlinarith
    by_contra hc
    linarith
  have neq3 : 9 * x ^ 2 - 1 ≠ 0 := by 
    by_contra hc
    have eq1 :  x ^ 2 = 1 / 9 := by
      linarith
    have eq2 : y ^ 2 = 9 := by
      rw [yeq]
      rw [eq1]
      simp
    have aux : 9 - y ^ 2 = 0 := by linarith
    exact neq2 aux
  have eq1 : 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) = 
    1 + 35 / (37 - (9 * x ^ 2 + 4 / x ^ 2)) := by 
    calc 
      _ = 4 / (4 - x ^ 2) + (9 * x ^ 2) / (9 * x ^ 2 - 1)  := by 
        simp
        rw [yeq]
        field_simp
      _ = (- 9 * x ^ 4 + 72 * x ^ 2 - 4) / (- 9 * x ^ 4 + 37 * x ^ 2 - 4) := by 
        have aux : (-(9 * x ^ 4) + 37 * x ^ 2 - 4) = (4 - x ^ 2) * (9 * x ^ 2 - 1) := by
          ring
        have aux_neq : (-(9 * x ^ 4) + 37 * x ^ 2 - 4) ≠ 0 := by 
          rw [aux]
          apply mul_ne_zero neq1 neq3
        field_simp
        ring
      _ = (- 9 * x ^ 4 + 37 * x ^ 2 - 4 + 35 * x ^ 2) / (- 9 * x ^ 4 + 37 * x ^ 2 - 4) := by 
        ring_nf
      _ = _ := by 
        field_simp
        have eq_aux : (37 * x ^ 2 - (9 * x ^ 2 * x ^ 2 + 4)) = (-(9 * x ^ 4) + 37 * x ^ 2 - 4) := by ring
        rw [eq_aux]
        have aux : (-(9 * x ^ 4) + 37 * x ^ 2 - 4) = (4 - x ^ 2) * (9 * x ^ 2 - 1) := by
          ring
        have aux_neq : (-(9 * x ^ 4) + 37 * x ^ 2 - 4) ≠ 0 := by 
          rw [aux]
          apply mul_ne_zero neq1 neq3
        field_simp
  have ineq_aux (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0): 
    x + y  ≥ 2 * (x * y) ^ ((1:ℝ) / 2) := by
      have aux1 : x + y = |x + y| := by 
        unfold abs
        simp
        linarith
      have aux2 : 2 * (x * y) ^ ((1:ℝ) / 2) = |2 * (x * y) ^ ((1:ℝ) / 2)| := by 
        unfold abs
        simp
        positivity
      rw [aux1, aux2]
      refine sq_le_sq.mp ?_
      have aux3 : (2 * (x * y) ^ (1 / (2 : ℝ))) ^ 2 = 4 * x * y := by
        ring_nf
        congr
        have aux4 : ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℕ)
          = ((x * y) ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by norm_cast
        rw [aux4, ←Real.rpow_mul (by positivity) (1 / (2 : ℝ)) 2 (x := x * y)]
        simp
      rw [aux3]
      nlinarith [sq_nonneg (x - y)]
  have ineq : ((9 * x ^ 2) + (4 / x ^ 2)) ≥ 12 := by 
    calc 
      _ ≥ 2 * ((9 * x ^ 2) * (4 / x ^ 2)) ^ ( 1 / (2 : ℝ)) := by 
        refine ineq_aux (9 * x ^ 2) (4 / x ^ 2) ?_ ?_
        positivity
        positivity
      _ = 12 := by 
        have aux : 9 * x ^ 2 * (4 / x ^ 2) = 36 := by 
          field_simp
          ring_nf
        rw [aux]
        have aux2 : (36 : ℝ) ^ (1 / (2 : ℝ)) = 6 := by  
          refine (eq_rpow_inv ?_ ?_ ?_).mp ?_
          positivity
          positivity
          norm_num
          simp
          norm_num
        rw [aux2]
        norm_num
  have ineq2 : (37 - (9 * x ^ 2 + 4 / x ^ 2)) ≤ 25 := by 
    linarith
  have ineq3 : 35 / (37 - (9 * x ^ 2 + 4 / x ^ 2)) ≥ 35 / 25 := by
    refine div_le_div_of_nonneg_left ?_ ?_ ineq2
    positivity
    by_contra hc
    simp at hc
    have ineq_neg : 37 - (9 * x ^ 2 + 4 / x ^ 2) ≤ 0 := by linarith
    have ineq_neg2 : 35 / (37 - (9 * x ^ 2 + 4 / x ^ 2)) ≤ 0 := by 
      refine div_nonpos_of_nonneg_of_nonpos ?_ ineq_neg
      positivity
    have ineq4 : 1 + 35 / (37 - (9 * x ^ 2 + 4 / x ^ 2)) ≤ 1 := by 
      linarith
    have ineq5: 4 / (4 - x ^ 2) + 9 / (9 - y ^ 2) ≥ 2 := by 
      have aux1 : 4 / (4 - x ^ 2) ≥ 1 := by 
        refine (one_le_div₀ ?_).mpr ?_
        nlinarith
        nlinarith
      have aux2 : 9 / (9 - y ^ 2) ≥ 1 := by
        refine (one_le_div₀ ?_).mpr ?_
        nlinarith
        nlinarith
      linarith
    rw [←eq1] at ineq4
    linarith
  rw [hy, eq1]
  linarith
import Mathlib
set_option maxRecDepth 5000
/- 3. Do there exist integers $x$ and $y$ such that $x^{2}+2012=y^{2}$? Justify your claim. If such numbers exist, determine all of them. -/
theorem algebra_193512 : {(x, y) : ℤ × ℤ | x ^ 2 + 2012 = y ^ 2} = {(502, 504), (-502, 504), (502, -504), (-502, -504)}:= by
  -- Prove set equality by showing membership equivalence
  ext ⟨x, y⟩
  constructor
  -- Forward direction: if x² + 2012 = y², then (x,y) is one of the four solutions
  .
    intro h
    simp at h
    -- Rearrange equation to factored form: (y-x)(y+x) = 2012
    replace h : (y - x) * (y + x) = 2012:= by linarith
    -- Convert to natural number absolute values for divisibility analysis
    have h1 : (y - x).natAbs * (y + x).natAbs = 2012:= by
      zify
      rw [show |y - x| * |y + x| = |(y - x) * (y + x)| by exact Eq.symm (abs_mul (y - x) (y + x))]
      rw [h]
      norm_num
    -- Show that |y-x| divides 2012
    have h2 : (y - x).natAbs ∈ Nat.divisors 2012:= by
      suffices (y - x).natAbs ∣ 2012 by refine Nat.mem_divisors.mpr ⟨this, by norm_num⟩
      rw [←h1]
      simp
    -- Compute all divisors of 2012
    have h3 : Nat.divisors 2012 = {1, 2, 4, 503, 1006, 2012}:= by native_decide
    rw [h3] at h2
    clear h3
    simp at h2
    -- Case analysis on each possible divisor
    rcases h2 with h2 | h2 | h2 | h2 | h2 | h2
    all_goals
      zify at h2
    -- Case 1: |y-x| = 1
    .
      replace h2 : y - x = 1 ∨ y - x = -1:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 1 leads to 2y = 2013 (impossible for integer y)
      .
        rw [h2] at h
        replace h : 2 * y = 2013:= by linarith
        omega
      -- Subcase: y-x = -1 leads to 2y = -2013 (impossible for integer y)
      .
        rw [h2] at h
        replace h : 2 * y = -2013:= by linarith
        omega
    -- Case 2: |y-x| = 2
    .
      replace h2 : y - x = 2 ∨ y - x = -2:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 2 gives solution (502, 504)
      .
        rw [h2] at h
        replace h2 : y = 504:= by linarith
        replace h1 : x = 502:= by linarith
        subst x y
        simp
      -- Subcase: y-x = -2 gives solution (-502, -504)
      .
        rw [h2] at h
        replace h2 : y = -504:= by linarith
        replace h1 : x = -502:= by linarith
        subst x y
        simp
    -- Case 3: |y-x| = 4
    .
      replace h2 : y - x = 4 ∨ y - x = -4:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 4 leads to 2y = 507 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = 507:= by linarith
        omega
      -- Subcase: y-x = -4 leads to 2y = -507 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = -507:= by linarith
        omega
    -- Case 4: |y-x| = 503
    .
      replace h2 : y - x = 503 ∨ y - x = -503:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 503 leads to 2y = 507 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = 507:= by linarith
        omega
      -- Subcase: y-x = -503 leads to 2y = -507 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = -507:= by linarith
        omega
    -- Case 5: |y-x| = 1006
    .
      replace h2 : y - x = 1006 ∨ y - x = -1006:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 1006 gives solution (-502, 504)
      .
        rw [h2] at h
        replace h2 : y = 504:= by linarith
        replace h1 : x = -502:= by linarith
        subst x y
        simp
      -- Subcase: y-x = -1006 gives solution (502, -504)
      .
        rw [h2] at h
        replace h2 : y = -504:= by linarith
        replace h1 : x = 502:= by linarith
        subst x y
        simp
    -- Case 6: |y-x| = 2012
    .
      replace h2 : y - x = 2012 ∨ y - x = -2012:= by exact abs_eq_abs.mp h2
      rcases h2 with h2 | h2
      -- Subcase: y-x = 2012 leads to 2y = 2013 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = 2013:= by linarith
        omega
      -- Subcase: y-x = -2012 leads to 2y = -2013 (impossible for integer y)
      .
        rw [h2] at h
        replace h2 : 2 * y = -2013:= by linarith
        omega
  -- Backward direction: verify that each of the four solutions satisfies the equation
  .
    intro h
    simp at h
    -- Check each of the four proposed solutions
    rcases h with h | h | h | h
    all_goals
      rcases h with ⟨hx, hy⟩
      subst x y
      simp

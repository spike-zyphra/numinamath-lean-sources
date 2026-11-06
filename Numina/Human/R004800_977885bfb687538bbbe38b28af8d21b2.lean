import Mathlib

/- Three. (Full marks 20 points) Given the equation $x^{2}+m x-m+1=0$ (where $m$ is an integer) has two distinct positive integer roots. Find the value of $m$.

---

The translation maintains the original format and line breaks as requested. -/
theorem algebra_328008 {m : ℤ} (h : ∃ x y : ℕ, x ≠ y ∧ x > 0 ∧ y > 0 ∧ x^2 + m * x - m + 1 = 0 ∧ y^2 + m * y - m + 1 = 0) :
    m = -5 := by
  -- Extract the two distinct positive integer roots and their properties
  rcases h with ⟨x, y, hxy, hxpos, hypos, hx, hy⟩
  -- Assign the equations for both roots to named variables
  have eq1 := hx
  have eq2 := hy
  -- Convert natural number expressions to integer expressions
  zify at eq1 eq2
  -- Prove that (x-y)*(x+y+m) = 0 by manipulating the equations
  have h_eq : ((x : ℤ) - (y : ℤ)) * ((x : ℤ) + (y : ℤ) + m) = 0 := by
    ring_nf at eq1 eq2
    nlinarith [eq1, eq2]
  -- Since the product is zero, one of the factors must be zero
  cases' (mul_eq_zero.mp h_eq) with hxy1 hxy2
  · -- Case 1: x - y = 0, which means x = y, contradicting our assumption that x ≠ y
    have h_contra : (x : ℤ) = (y : ℤ) := by linarith
    have h_contra' : x = y := by
      exact_mod_cast h_contra
    exact absurd h_contra' hxy
  · -- Case 2: x + y + m = 0, which means m = -(x + y)
    have h_sum : (x : ℤ) + (y : ℤ) + m = 0 := by linarith
    have h_m : m = -((x : ℤ) + (y : ℤ)) := by linarith
    -- Substitute the value of m into the first equation
    rw [h_m] at eq1
    -- Derive that x*y - x - y = 1
    have h_eq2 : (x : ℤ) * (y : ℤ) - (x : ℤ) - (y : ℤ) = 1 := by
      nlinarith [eq1, h_sum]
    -- Rewrite as (x-1)*(y-1) = 2
    have h_mul : ((x : ℤ) - 1) * ((y : ℤ) - 1) = 2 := by
      nlinarith [h_eq2]
    -- Prove that x-1 ≥ 0
    have hx1 : (x : ℤ) - 1 ≥ 0 := by nlinarith [hxpos]
    -- Prove that y-1 ≥ 0
    have hy1 : (y : ℤ) - 1 ≥ 0 := by nlinarith [hypos]
    -- Prove that x-1 > 0 by contradiction
    have hx2 : (x : ℤ) - 1 > 0 := by
      by_contra h
      push_neg at h
      have : ((x : ℤ) - 1) * ((y : ℤ) - 1) ≤ 0 := by nlinarith
      linarith [h_mul, this]
    -- Prove that y-1 > 0 by contradiction
    have hy2 : (y : ℤ) - 1 > 0 := by
      by_contra h
      push_neg at h
      have : ((x : ℤ) - 1) * ((y : ℤ) - 1) ≤ 0 := by nlinarith
      linarith [h_mul, this]
    -- Prove that x-1 ≤ 2 since (x-1)*(y-1) = 2 and y-1 > 0
    have h_x_minus_1 : (x : ℤ) - 1 ≤ 2 := by
      nlinarith [show ((x : ℤ) - 1) * ((y : ℤ) - 1) = 2 from h_mul, hy2]
    -- Prove that y-1 ≤ 2 since (x-1)*(y-1) = 2 and x-1 > 0
    have h_y_minus_1 : (y : ℤ) - 1 ≤ 2 := by
      nlinarith [show ((x : ℤ) - 1) * ((y : ℤ) - 1) = 2 from h_mul, hx2]
    -- Since x-1 is a positive integer ≤ 2, it must be either 1 or 2
    have h_x : (x : ℤ) - 1 = 1 ∨ (x : ℤ) - 1 = 2 := by
      interval_cases (x : ℤ) - 1 <;> omega
    -- Since y-1 is a positive integer ≤ 2, it must be either 1 or 2
    have h_y : (y : ℤ) - 1 = 1 ∨ (y : ℤ) - 1 = 2 := by
      interval_cases (y : ℤ) - 1 <;> omega
    -- Consider the possible values of x-1
    rcases h_x with hxv1 | hxv2
    · -- Case 2.1: x-1 = 1, which means x = 2
      have hx_eq : (x : ℤ) = 2 := by linarith
      -- Consider the possible values of y-1
      rcases h_y with hyv1 | hyv2
      · -- Case 2.1.1: y-1 = 1, which means y = 2
        -- This leads to a contradiction since x and y must be distinct
        exfalso
        have : ((x : ℤ) - 1) * ((y : ℤ) - 1) = 1 * 1 := by
          rw [hxv1, hyv1]
        linarith [h_mul, this]
      · -- Case 2.1.2: y-1 = 2, which means y = 3
        have hy_eq : (y : ℤ) = 3 := by linarith
        -- Calculate m using x + y + m = 0
        rw [hx_eq, hy_eq] at h_sum
        have hm : (m : ℤ) = -5 := by linarith
        exact_mod_cast hm
    · -- Case 2.2: x-1 = 2, which means x = 3
      have hx_eq : (x : ℤ) = 3 := by linarith
      -- Consider the possible values of y-1
      rcases h_y with hyv1 | hyv2
      · -- Case 2.2.1: y-1 = 1, which means y = 2
        have hy_eq : (y : ℤ) = 2 := by linarith
        -- Calculate m using x + y + m = 0
        rw [hx_eq, hy_eq] at h_sum
        have hm : (m : ℤ) = -5 := by linarith
        exact_mod_cast hm
      · -- Case 2.2.2: y-1 = 2, which means y = 3
        -- This leads to a contradiction since x and y must be distinct
        exfalso
        have : ((x : ℤ) - 1) * ((y : ℤ) - 1) = 2 * 2 := by
          rw [hxv2, hyv2]
        linarith [h_mul, this]

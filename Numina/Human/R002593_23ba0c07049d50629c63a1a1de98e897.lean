import Mathlib.Tactic

-- A positive number $x$ has the property that $x\%$ of $x$ is $4$.  What is $x$?

theorem algebra_1159
  (x : ℝ)
  (h : x > 0 )
  (percent : x * 0.01 * x = 4 ) :
  x = 20 := by
    -- multiply both sides by 100
    have h_mul_100 : x * 0.01 * x * 100 = 4 * 100 := by
      exact congrFun (congrArg HMul.hMul percent) 100
    -- simplify the left side
    have h₁ : x * 0.01 * x * 100 = x ^ 2 := by
      calc x * 0.01 * x * 100 = x * x * 100 * 0.01 := by ring
      _ = x * x * 1 := by ring
      _ = x * x := by ring
      _ = x ^ 2 := by ring
    -- 4 * 100 = 400
    have h₂ : 4 * 100  = (400 : ℝ) := by norm_num
    -- simplify h_mul_100, the original equation to get x ^ 2 = 400
    have h₃ : x ^ 2 = 400 := by
      rw [h₁] at h_mul_100
      calc x ^ 2 = 4 * 100 := by exact h_mul_100
      _ = 400  := by exact h₂
    -- simplify 400 as 20 ^ 2 in the original equation
    have h₄ : x ^ 2 = 20 ^ 2 := by
      calc x ^ 2 = 400 := by exact h₃
      _ = 20 * 20 := by
        refine (Real.sqrt_eq_iff_mul_self_eq ?hx ?hy).mp ?_
        simp; simp; refine (Real.sqrt_eq_iff_mul_self_eq_of_pos ?h).mpr ?_
        simp; linarith
      _ = 20 ^ 2 := by exact Eq.symm (pow_two 20)
    -- finally, have x = 20 from x ^ 2 = 20 ^ 2 by using principal square root
    calc x = √(x ^ 2) := by refine Eq.symm (Real.sqrt_sq ?h); exact le_of_lt h
    _ = √(20 ^ 2) := by exact congrArg Real.sqrt h₄
    _ = |20|  := by exact Real.sqrt_sq_eq_abs 20
    _ = 20 := by
      refine abs_eq_self.mpr ?_
      exact Nat.ofNat_nonneg' 20
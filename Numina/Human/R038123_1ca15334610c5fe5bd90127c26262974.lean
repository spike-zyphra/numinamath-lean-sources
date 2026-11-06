import Mathlib

/- Find all solutions to
\[\sqrt{x + 3 - 4 \sqrt{x - 1}} + \sqrt{x + 8 - 6 \sqrt{x - 1}} = 1.\] -/
theorem algebra_11065 :
  {x | x - 1 ≥ 0 ∧ x + 3 - 4 * √(x - 1) ≥ 0 ∧ x + 8 - 6 * √(x - 1) ≥ 0 ∧
      √(x + 3 - 4 * √(x - 1)) + √(x + 8 - 6 * √(x - 1)) = 1} =
  Set.Icc 5 10 := by
  apply Set.ext
  intro x
  simp
  constructor <;> intro hx
  -- Note that for the expression to be defined, we must have $x \ge 1.$ 
  rcases hx with ⟨hx1,hx2,hx3,hx4⟩
  -- Let $y = \sqrt{x - 1}.$ Then $y^2 = x - 1,$ so $x = y^2 + 1.
  let y : ℝ := √ (x - 1)
  have hy1 : y ^ 2 = x - 1 := Real.sq_sqrt (by linarith [hx1])
  -- We can then write the given equation as [\sqrt{y^2 - 4y + 4} + \sqrt{y^2 - 6y + 9} = 1.]
  have hy2 : x = y ^ 2 + 1 := by linarith
  rw [hy2] at hx4
  have hy3 : √ (y ^ 2) = y := congrArg Real.sqrt hy1
  simp [hy3] at hx4
  ring_nf at hx4
  -- Thus, $\sqrt{(y - 2)^2} + \sqrt{(y - 3)^2} = 1,$ or [|y - 2| + |y - 3| = 1.]
  have hy4 : √((y-2)^2) + √((y-3)^2) = 1 := by rw [← hx4] ;ring_nf
  -- If $y &lt; 2,$ then [|y - 2| + |y - 3| = 2 - y + 3 - y = 5 - 2y &gt; 1.]
  by_cases h1 : y < 2
  · have h2 : √((y - 2) ^ 2) = 2 - y := by 
      refine Real.sqrt_eq_cases.mpr ?_
      left ;ring_nf ;simp ;nlinarith [h1]
    have h3 : √((y - 3) ^ 2) = 3 - y := by
      refine Real.sqrt_eq_cases.mpr ?_
      left ;ring_nf ;simp ;nlinarith [h1]
    rw [h2,h3] at hy4
    ring_nf at hy4 ;nlinarith
  -- If $y &gt; 3,$ then [|y - 2| + |y - 3| = y - 2 + y - 3 = 2y - 5 &gt; 1.]
  by_cases h4 : y > 3
  · have h5 : √((y - 2) ^ 2) = y - 2 := by 
      refine Real.sqrt_sq ?_ ;nlinarith
    have h6 : √((y - 3) ^ 2) = y - 3 := by
      refine Real.sqrt_sq ?_ ;nlinarith 
    rw [h5,h6] at hy4 ;ring_nf at hy4 ;nlinarith
  constructor
  · nlinarith
  nlinarith
  -- If $2 \le y \le 3,$ then [|y - 2| + |y - 3| = y - 2 + 3 - y = 1,]so we must have $2 \le y \le 3.$ Then [2 \le \sqrt{x - 1} \le 3,]so [4 \le x - 1 \le 9,]or $5 \le x \le 10.$ Thus, the solution is {$x | 5 \le x \le 10$}
  constructor
  · linarith
  have hx1 : (√(x - 1)) ^ 2 = x - 1 := by
    refine Real.sq_sqrt ?_ ;linarith
  have hx2 : x + 3 - 4 * √(x - 1) = (√(x - 1) - 2) ^ 2 := by
    rw [pow_two,sub_mul,mul_sub,← pow_two,hx1]
    ring
  have hx3 : 0 ≤ x + 3 - 4 * √(x - 1) := by
    rw [hx2] ;exact sq_nonneg (√(x - 1) - 2)
  have hx4 : x + 8 - 6 * √(x - 1) = (√(x - 1) - 3) ^ 2 := by
    rw [pow_two,sub_mul,mul_sub,← pow_two,hx1]
    ring
  have hx5 : 0 ≤ x + 8 - 6 * √(x - 1) := by
    rw [hx4] ;exact sq_nonneg (√(x - 1) - 3)
  constructor
  · linarith
  constructor
  · linarith
  rw [hx2,hx4]
  have hx6 : √((√(x - 1) - 2) ^ 2) = (√(x - 1) - 2) := by
    refine Real.sqrt_sq ?_
    simp
    refine (Real.le_sqrt' ?_).mpr ?_
    simp ;linarith
  have hx7 : √((√(x - 1) - 3) ^ 2) = (3 - √(x - 1)) := by
    refine Real.sqrt_eq_cases.mpr ?_
    left ;constructor ;ring
    simp
    refine Real.sqrt_le_iff.mpr ?_
    simp ;linarith
  rw [hx6,hx7] ;ring
  
  

    

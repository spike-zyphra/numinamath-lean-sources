import Mathlib

/- Suppose that $a, b, c, d$ are positive real numbers satisfying $(a+c)(b+d)=a c+b d$. Find the smallest possible value of  $$ \\frac{a}{b}+\\frac{b}{c}+\\frac{c}{d}+\\frac{d}{a} -/
theorem algebra_23933 :
    IsLeast {a / b + b / c + c / d + d / a | (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (_ : 0 < a) (_ : 0 < b) (_ : 0 < c) (_ : 0 < d) (_ : (a + c) * (b + d) = a * c + b * d)} 8 := by
  -- Two goals to prove
  -- 1. There exists a, b, c, d such that the equation holds, and the value is 8
  -- 2. For any a, b, c, d, the value is at least 8
  constructor
  . -- First goal
    -- Set a = 1, b = 2 + √3, c = 1, d = 2 + √3
    dsimp
    use 1, 2 + √3, 1, 2 + √3
    -- Six subgoals to prove, but all are trivial after simplification
    constructorm* ∃ _, _
    . -- Show 1 / (2 - √3) = 2 + √3
      have h : 1 = (2 + √3) * (2 - √3) := by ring_nf; norm_num
      nth_rw 1 3 [h]
      simp [show 2 + √3 ≠ 0 by positivity]
      ring
    . ring_nf
      simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
      ring
    . positivity
    . simp
    . positivity
    . simp
  . -- Second goal
    rintro x ⟨a, b, c, d, apos, bpos, cpos, dpos, h, rfl⟩
    -- Prove the AM-GM inequality
    have AMGM (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : x + y ≥ 2 * √(x * y) := by
      nth_rw 1 [show x = √x^2 by simp [le_of_lt hx], show y = √y^2 by simp [le_of_lt hy], Real.sqrt_mul (le_of_lt hx)]
      linarith only [sq_nonneg (√x - √y)]
    calc a / b + b / c + c / d + d / a
         _ = (a / b + c / d) + (b / c + d / a) := by ac_rfl
         -- Use AM-GM inequality
         _ ≥ 2 * √((a / b) * (c / d)) + 2 * √((b / c) * (d / a)) := by linarith only [AMGM (a / b) (c / d) (div_pos apos bpos) (div_pos cpos dpos), AMGM (b / c) (d / a) (div_pos bpos cpos) (div_pos dpos apos)]
         -- Simplify the expression
         _ = 2 * (a * c + b * d) / √(a * b * c * d) := by
            -- Cancel the denominators
            field_simp
            ring_nf
            -- √x^3 = x * √x
            have H {x} (h : x > 0) : √x ^ 3 = x * √x := by
              rw [pow_succ, Real.sq_sqrt (le_of_lt h)]
            rw [H apos, H bpos, H cpos, H dpos]
            ring
         -- Use the given equation
         _ = 2 * ((a + c) * (b + d)) / √(a * b * c * d) := by rw [h]
         -- Apply the AM-GM inequality
         _ ≥ 2 * ((2 * √(a * c)) * (2 * √(b * d))) / √(a * b * c * d) := by
            have h1 := AMGM a c apos cpos
            have h2 := AMGM b d bpos dpos
            have h3 : 2 * ((a + c) * (b + d)) ≥ 2 * ((2 * √(a * c)) * (2 * √(b * d))) := by nlinarith [h1, h2, show 2 * √(a * c) > 0 by positivity, show 2 * √(b * d) > 0 by positivity]
            exact (div_le_div_iff_of_pos_right (by positivity)).2 h3
         _ = 8 := by
            -- Break down expression of the form √(_ * _)
            rw [Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul]
            -- Now it is trivial
            ring_nf
            field_simp
            -- Some positivity conditions
            all_goals
              positivity

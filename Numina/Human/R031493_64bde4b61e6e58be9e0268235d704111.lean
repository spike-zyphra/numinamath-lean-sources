import Mathlib

open Real

/- Let $a$ and $b$ be real numbers such that $a > b > 0.$  Determine the minimum value of
\[a + \frac{1}{b(a - b)}.\] -/
theorem algebra_21934:
  IsLeast {u:ℝ | ∃(a b:ℝ), u = a + 1/(b*(a-b)) ∧ 0 < a ∧ 0 < b ∧ b < a} 3 := by
  -- by AM-GM, following holds.
  have am_gm3{x y z:ℝ}(posx: 0 < x)(posy: 0 < y)(posz: 0 < z):
    x+y+z ≥ 3 * (x*y*z)^(1/3:ℝ) := by
    have hh1: (1/3:ℝ)+1/3+1/3 = 1 := by ring
    have hh2: (x*y*z)^(1/3:ℝ) = x^(1/3:ℝ)*y^(1/3:ℝ)*z^(1/3:ℝ) := by
      have tt1: x^(1/3:ℝ)*y^(1/3:ℝ)=(x*y)^(1/3:ℝ) := by
        symm
        apply mul_rpow (le_of_lt posx) (le_of_lt posy)
      have tt2: 0 < x*y := by
        apply mul_pos posx posy
      rw [mul_rpow (le_of_lt tt2) (le_of_lt posz)]
      rw [tt1]
    have hh3: (x*y*z)^(1/3:ℝ) ≤ (x+y+z)/3 := by
      have tt1: (x+y+z)/3 = (1/3)*x + (1/3)*y + (1/3)*z := by ring
      rw [hh2, tt1]
      apply geom_mean_le_arith_mean3_weighted
        (by norm_num) (by norm_num) (by norm_num)
        (le_of_lt posx) (le_of_lt posy) (le_of_lt posz) hh1
    linarith [hh3]
  -- to use AM-GM, we rewrite a + 1/(b(a-b)) as b + (a-b) + 1/(b(a-b))
  have h1(a b: ℝ): a + (a - b)⁻¹ * b⁻¹ = b + (a-b) + (a-b)⁻¹*b⁻¹ := by ring
  -- proceed to the problem
  rw [IsLeast, lowerBounds]; simp; constructor
  · -- to reach minimum, we require AM-GM take equal, therefore b=(a-b)=1/(b(a-b))
    -- so a=2, b=1.
    use 2,1; norm_num
  · -- this direction, we use AM-GM to show 3 is a lower bound.
    intro u a b hu posa posb blta
    rw [h1 a b] at hu
    have: 3 * (b * (a-b) * ((a-b)⁻¹*b⁻¹))^(1/3:ℝ) = 3 := by
      have: b*(a-b)* ((a-b)⁻¹*b⁻¹) = 1 := by
        have hh1: a-b ≠ 0 := by
          apply ne_of_gt (by linarith [blta])
        have hh2: b ≠ 0 := by linarith [posb]
        field_simp [hh1, hh2]; ring
      rw [this]; simp
    rw [← this, hu]
    apply am_gm3 posb (by linarith [blta])
    apply mul_pos
    · apply inv_pos.mpr (by linarith [blta])
    · apply inv_pos.mpr posb
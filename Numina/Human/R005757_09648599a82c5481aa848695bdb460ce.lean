import Mathlib
/-Points $A, B, C, D$ lie on a circle in that order such that $\frac{A B}{B C}=\frac{D A}{C D}$. If $A C=3$ and $B D=B C=4$, find $A D$. -/

theorem geometry_609751 (AD AB BC CD AC BD : ℚ)
  (h_ratio : AB / BC = AD / CD)
  (h_BC    : BC = 4)
  (h_AC    : AC = 3)
  (h_BD    : BD = 4)
  (h_CD    : CD ≠ 0)
  (h_ptolemy : AB * CD + BC * AD = AC * BD)
  : AD = 3/2 := by
  -- Cross-multiplying the given ratio AB/BC = AD/CD gives AB*CD = AD*BC
  have h1 : AB * CD = AD * BC := by
    field_simp [h_ratio, h_BC, h_AC, h_BD, mul_comm] at h_ratio ⊢
    exact h_ratio
  -- Substitute AB*CD with AD*BC in Ptolemy's theorem equation
  rw [h1] at h_ptolemy
  -- Combine like terms in Ptolemy's theorem equation to get 2*AD*BC = AC*BD
  have h2 : 2 * AD * BC = AC * BD := by
    field_simp [h_ptolemy, h_BC, h_AC, h_BD, mul_comm] at h_ptolemy ⊢
    linarith
  -- Substitute known values BC = 4, AC = 3, BD = 4 into the equation
  rw [h_BC, h_AC, h_BD] at h2
  -- Simplify the equation numerically to solve for AD
  norm_num at h2
  -- Conclude that AD = 3/2 using linear arithmetic
  linarith
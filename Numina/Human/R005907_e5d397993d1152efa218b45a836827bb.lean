import Mathlib
/- Over all real numbers $x$ and $y$ such that

$$
x^{3}=3 x+y \quad \text { and } \quad y^{3}=3 y+x
$$

compute the sum of all possible values of $x^{2}+y^{2}$. -/
theorem algebra_610653 (A : Finset ℝ) (hA : A = {a : ℝ| ∃ x y : ℝ, x ^ 3 = 3 * x + y ∧ y ^ 3 = 3 * y + x ∧ a = x ^ 2 + y ^ 2}) : ∑ a in A, a = 15:= by
  -- Prove that the set of all possible values of x^2 + y^2 is {0, 4, 8, 3}
  have h1 : {a : ℝ| ∃ x y : ℝ, x ^ 3 = 3 * x + y ∧ y ^ 3 = 3 * y + x ∧ a = x ^ 2 + y ^ 2} = {0, 4, 8, 3}:= by
    ext a
    constructor
    -- Forward direction: prove any solution must be in {0, 4, 8, 3}
    .
      intro h
      simp at h
      rcases h with ⟨x, y, hx, hy, ha⟩
      subst a
      -- Case analysis on whether x - y = 0 or x + y = 0
      by_cases h1 : x - y = 0 ∨ x + y = 0
      .
        rcases h1 with h1 | h1
        -- Case 1: x = y
        .
          replace h1 : x = y:= by linarith
          subst x
          replace hx : y * (y ^ 2 - 4) = 0:= by linarith
          simp at hx
          rcases hx with hx | hx
          -- Subcase: y = 0
          .
            subst y
            simp
          -- Subcase: y^2 = 4
          .
            replace hx : y ^ 2 = 4:= by linarith
            rw [hx]
            simp
            norm_num
        -- Case 2: x = -y
        .
          replace h1 : x = -y:= by linarith
          subst x
          replace hx : y * (y ^ 2 - 2) = 0:= by linarith
          simp at hx
          rcases hx with hx | hx
          -- Subcase: y = 0
          .
            subst y
            simp
          -- Subcase: y^2 = 2
          .
            replace hx : y ^ 2 = 2:= by linarith
            ring_nf
            rw [hx]
            simp
            norm_num
      -- Case 3: Neither x - y = 0 nor x + y = 0
      .
        simp at h1
        rcases h1 with ⟨h1, h2⟩
        replace hx : (x - y) * (x ^ 2 + y ^ 2 + x * y - 2) = 0:= by linarith
        replace hy : (x + y) * (x ^ 2 + y ^ 2 - x * y - 4) = 0:= by linarith
        simp [h1] at hx
        simp [h2] at hy
        replace hx : x ^ 2 + y ^ 2 = 3:= by linarith
        rw [hx]
        simp
    -- Backward direction: prove each element in {0, 4, 8, 3} is a valid solution
    .
      intro h
      simp at h
      rcases h with h | h | h | h
      -- Case: a = 0
      .
        subst a
        simp
        use 0, 0
        simp
      -- Case: a = 4
      .
        subst a
        simp
        use √2, -√2
        constructor
        .
          rw [show √2 ^ 3 = √2 ^ 2 * √2 by ring]
          field_simp
          linarith
        .
          constructor
          .
            ring_nf
            rw [show √2 ^ 3 = √2 ^ 2 * √2 by ring]
            field_simp
            linarith
          .
            ring_nf
            field_simp
            linarith
      -- Case: a = 8
      .
        subst a
        use 2, 2
        simp
        norm_num
      -- Case: a = 3
      .
        subst a
        simp
        use ((1 + √5) / 2), ((1 - √5) / 2)
        ring_nf
        constructor
        .
          rw [show √5 ^ 3 = √5 ^ 2 * √5 by ring]
          field_simp
          linarith
        .
          constructor
          .
            rw [show √5 ^ 3 = √5 ^ 2 * √5 by ring]
            field_simp
            linarith
          .
            field_simp
            linarith
  -- Final steps: Use the proven equality to show the sum equals 15
  rw [h1] at hA
  clear h1
  replace hA : A = {0, 4, 8, 3}:= by refine Finset.coe_inj.mp (by simp [hA])
  rw [hA]
  simp
  linarith

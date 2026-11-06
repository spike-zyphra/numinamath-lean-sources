import Mathlib
open Real
set_option maxHeartbeats 800000
/- 161*. Prove the identity:

$$
\sqrt{A \pm \sqrt{\bar{B}}}=\sqrt{\frac{A+\sqrt{A^{2}-B}}{2}} \pm \sqrt{\frac{A-\sqrt{A^{2}-B}}{2}}
$$

34 -/
theorem algebra_276278 {A B : ℝ} (hA : A ≥ 0) (hB : B ≥ 0)
    (hAB : A^2 ≥ B) :
    √(A + √B) = √((A + √(A^2 - B)) / 2) +
    √((A - √(A^2 - B)) / 2) ∧
    √(A - √B) = √((A + √(A^2 - B)) / 2) -
    √((A - √(A^2 - B)) / 2) := by

  -- Prove that √(A² - B) is non-negative
  have h1 : √(A ^ 2 - B) ≥ 0 := by
    apply Real.sqrt_nonneg

  -- Prove that (A + √(A² - B))/2 is non-negative
  have h2 : (A + √(A ^ 2 - B)) / 2 ≥ 0 := by
    have h3 : √(A ^ 2 - B) ≥ 0 := by
      apply Real.sqrt_nonneg
    linarith [hA, h3]

  -- Prove that (A - √(A² - B))/2 is non-negative
  have h4 : (A - √(A ^ 2 - B)) / 2 ≥ 0 := by
    have h5 : √(A ^ 2 - B) ≤ A := by
      have h6 : √(A ^ 2 - B) ≤ √(A ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      rw [Real.sqrt_sq (by linarith)] at h6
      linarith
    linarith [hA, h5]

  -- Prove the first part of the identity: √(A + √B) = √((A + √(A² - B))/2) + √((A - √(A² - B))/2)
  have h7 : √(A + √B) = √((A + √(A^2 - B)) / 2) + √((A - √(A^2 - B)) / 2) := by
    -- Establish that both square roots are non-negative
    have h8 : √((A + √(A ^ 2 - B)) / 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    have h9 : √((A - √(A ^ 2 - B)) / 2) ≥ 0 := by
      apply Real.sqrt_nonneg
    -- Prove the identity by squaring both sides
    have h10 : (√((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2)) ^ 2 = (√(A + √B)) ^ 2 := by
      -- Expand the square of the sum
      have h11 : (√((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2)) ^ 2 =
        (√((A + √(A ^ 2 - B)) / 2)) ^ 2 + (√((A - √(A ^ 2 - B)) / 2)) ^ 2 + 2 * (√((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2)) := by ring
      -- Simplify the right side
      have h12 : (√(A + √B)) ^ 2 = A + √B := by
        exact Real.sq_sqrt (by linarith [hA, Real.sqrt_nonneg B])
      rw [h11, h12]
      -- Simplify the squares of the square roots
      have h13 : (√((A + √(A ^ 2 - B)) / 2)) ^ 2 = (A + √(A ^ 2 - B)) / 2 := by
        exact Real.sq_sqrt (by linarith [h2])
      have h14 : (√((A - √(A ^ 2 - B)) / 2)) ^ 2 = (A - √(A ^ 2 - B)) / 2 := by
        exact Real.sq_sqrt (by linarith [h4])
      -- Prove that the product of the square roots equals √B/2
      have h15 : √((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2) = √B / 2 := by
        calc
          √((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2)
              = √(((A + √(A ^ 2 - B)) / 2) * ((A - √(A ^ 2 - B)) / 2)) := by
                rw [←Real.sqrt_mul (by linarith [h2])]
          _ = √((A ^ 2 - (√(A ^ 2 - B)) ^ 2) / 4) := by ring_nf
          _ = √((A ^ 2 - (A ^ 2 - B)) / 4) := by
            have h16 : (√(A ^ 2 - B)) ^ 2 = A ^ 2 - B := Real.sq_sqrt (by nlinarith)
            rw [h16]
          _ = √(B / 4) := by ring_nf
          _ = √B / √4 := by
            field_simp [Real.sqrt_div]
          _ = √B / 2 := by
            have h17 : √(4 : ℝ) = 2 := by
              rw [Real.sqrt_eq_cases]
              norm_num
            rw [h17]
      linarith [h13, h14, h15]
    -- Establish that both sides are non-negative
    have h19 : √(A + √B) ≥ 0 := by
      apply Real.sqrt_nonneg
    -- Complete the proof using the fact that if x² = y² and x,y ≥ 0, then x = y
    have h20 : √((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2) = √(A + √B) := by
      have h22 : √((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2) ≥ 0 := by
        linarith [h8, h9]
      have h23 : √(A + √B) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h24 : √((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2) = √(A + √B) := by
        nlinarith [sq_nonneg (√((A + √(A ^ 2 - B)) / 2) + √((A - √(A ^ 2 - B)) / 2) - √(A + √B)), h22, h23]
      exact h24
    linarith

  -- Prove the second part of the identity: √(A - √B) = √((A + √(A² - B))/2) - √((A - √(A² - B))/2)
  have h29 : √(A - √B) = √((A + √(A^2 - B)) / 2) - √((A - √(A^2 - B)) / 2) := by
    -- Establish the ordering of the square roots
    have h30 : √((A + √(A ^ 2 - B)) / 2) ≥ √((A - √(A ^ 2 - B)) / 2) := by
      exact Real.sqrt_le_sqrt (by linarith)
    -- Prove the identity by squaring both sides
    have h36 : (√((A + √(A ^ 2 - B)) / 2) - √((A - √(A ^ 2 - B)) / 2)) ^ 2 = (√(A - √B)) ^ 2 := by
      -- Expand the square of the difference
      have h37 : (√((A + √(A ^ 2 - B)) / 2) - √((A - √(A ^ 2 - B)) / 2)) ^ 2 =
        (√((A + √(A ^ 2 - B)) / 2)) ^ 2 + (√((A - √(A ^ 2 - B)) / 2)) ^ 2 - 2 * (√((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2)) := by ring
      -- Simplify the right side
      have h38 : (√(A - √B)) ^ 2 = A - √B := by
        have h39 : A - √B ≥ 0 := by
          have h40 : √B ≤ A := by
            have h41 : √B ≤ √(A ^ 2) := by
              apply Real.sqrt_le_sqrt
              nlinarith [hAB]
            rw [Real.sqrt_sq (by linarith)] at h41
            linarith
          linarith [hA, h40]
        exact Real.sq_sqrt h39
      rw [h37, h38]
      -- Simplify the squares of the square roots
      have h42 : (√((A + √(A ^ 2 - B)) / 2)) ^ 2 = (A + √(A ^ 2 - B)) / 2 := by
        exact Real.sq_sqrt (by linarith [h2])
      have h43 : (√((A - √(A ^ 2 - B)) / 2)) ^ 2 = (A - √(A ^ 2 - B)) / 2 := by
        exact Real.sq_sqrt (by linarith [h4])
      -- Prove that the product of the square roots equals √B/2
      have h44 : √((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2) = √B / 2 := by
        calc
          √((A + √(A ^ 2 - B)) / 2) * √((A - √(A ^ 2 - B)) / 2)
              = √(((A + √(A ^ 2 - B)) / 2) * ((A - √(A ^ 2 - B)) / 2)) := by
                rw [←Real.sqrt_mul (by linarith [h2])]
          _ = √((A ^ 2 - (√(A ^ 2 - B)) ^ 2) / 4) := by ring_nf
          _ = √((A ^ 2 - (A ^ 2 - B)) / 4) := by
            have h45 : (√(A ^ 2 - B)) ^ 2 = A ^ 2 - B := Real.sq_sqrt (by nlinarith)
            rw [h45]
          _ = √(B / 4) := by ring_nf
          _ = √B / √4 := by
            field_simp [Real.sqrt_div]
          _ = √B / 2 := by
            have h46 : √(4 : ℝ) = 2 := by
              rw [Real.sqrt_eq_cases]
              norm_num
            rw [h46]
      linarith [h42, h43, h44]
    -- Establish that both sides are non-negative
    have h47 : √((A + √(A ^ 2 - B)) / 2) - √((A - √(A ^ 2 - B)) / 2) ≥ 0 := by
      linarith [h30]
    have h48 : √(A - √B) ≥ 0 := by
      apply Real.sqrt_nonneg
    -- Complete the proof using the fact that if x² = y² and x,y ≥ 0, then x = y
    have h49 : √((A + √(A ^ 2 - B)) / 2) - √((A - √(A ^ 2 - B)) / 2) = √(A - √B) := by
      nlinarith [sq_nonneg (√((A + √(A ^ 2 - B)) / 2) - √((A - √(A ^ 2 - B)) / 2) - √(A - √B)), h47, h48]
    linarith
  -- Combine both parts of the identity into the final result
  exact ⟨h7, h29⟩

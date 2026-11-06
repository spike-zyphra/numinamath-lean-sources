import Mathlib
/- 9. Let real numbers $A, B, C$ satisfy the inequality $A(x-y)(x-z)+B(y-z)(y-x)+C(z-x)(z-y) \geqslant 0$ (*) for any real numbers $x, y, z$. What conditions should $A, B, C$ meet? (The conditions should be both necessary and sufficient, and should be expressed using only equations or inequalities involving $A, B, C$). -/
theorem inequalities_225636 (A B C : ℝ) : (∀ x y z : ℝ, A * (x - y) * (x - z) + B * (y - z) * (y - x) + C * (z - x) * (z - y) ≥ 0) ↔ (A ≥ 0 ∧ B ≥ 0 ∧ C ≥ 0 ∧ A ^ 2 + B ^ 2 + C ^ 2 ≤ 2 * (A * B + B * C + C * A)):= by
  constructor
  -- Forward direction: assuming the inequality holds for all x, y, z, prove the conditions on A, B, C
  .
    intro h
    -- Test the inequality with specific values of x, y, z
    have h1:= h 0 0 1
    have h2:= h 0 1 0
    have h3:= h 1 0 0
    simp at h1 h2 h3
    -- From these specific cases, we get A ≥ 0, B ≥ 0, C ≥ 0
    refine ⟨h3, h2, h1, ?_⟩
    -- Rewrite the inequality in terms of two variables s and t
    replace h : ∀ s t : ℝ, A * s ^ 2 + (A - B + C) * s * t + C * t ^ 2 ≥ 0:= by
      intro s t
      specialize h s 0 (-t)
      simp at h
      linarith
    -- Case analysis on whether A = 0
    by_cases hA : A = 0
    -- Case 1: A = 0
    .
      subst A
      simp at h
      -- Subcase: Check if C = 0
      by_cases hC : C = 0
      -- Subcase 1.1: C = 0
      .
        subst C
        simp at h
        specialize h 1 1
        simp at h
        simp
        replace h : B = 0:= by linarith
        subst B
        simp
      -- Subcase 1.2: C ≠ 0
      .
        replace h1 : C > 0:= by positivity
        clear hC
        -- Simplify the inequality further
        replace h : ∀ a : ℝ, a * (-B + C) + C ≥ 0:= by
          intro a
          specialize h (a * √C) √C
          ring_nf at h
          field_simp at h
          replace h : C * (a * (-B + C) + C) ≥ 0:= by linarith
          exact nonneg_of_mul_nonneg_right h h1
        -- Check if -B + C = 0
        by_cases hB : -B + C = 0
        -- Subcase 1.2.1: -B + C = 0
        .
          replace hB : B = C:= by linarith
          subst B
          ring_nf
          linarith
        -- Subcase 1.2.2: -B + C ≠ 0
        .
          set e:= -B + C
          clear_value e
          specialize h (-2 * C / e)
          rw [show -2 * C / e * e = -2 * C by field_simp] at h
          linarith
    -- Case 2: A ≠ 0
    .
      replace h3 : A > 0:= by positivity
      clear hA
      -- Choose specific values of s and t to derive the inequality A² + B² + C² ≤ 2(AB + BC + CA)
      specialize h (-(A - B + C) / (2 * √A)) √A
      rw [show A * (-(A - B + C) / (2 * √A)) ^ 2 = (A - B + C) ^ 2 / 4 by field_simp ; ring_nf ; field_simp ; linarith] at h
      rw [show (A - B + C) * (-(A - B + C) / (2 * √A)) * √A = -(A - B + C) ^ 2 / 2 by ring_nf ; field_simp] at h
      rw [show √A ^ 2 = A by field_simp] at h
      linarith
  -- Reverse direction: assuming the conditions on A, B, C, prove the inequality holds for all x, y, z
  .
    intro h
    rcases h with ⟨hA, _, hC, h⟩
    intro x y z
    -- Substitute variables to simplify the expression
    set s:= x - y with hs
    set t:= y - z with ht
    clear_value s t
    rw [show x - z = s + t by linarith]
    rw [show y - x = -s by linarith]
    rw [show z - y = -t by linarith]
    rw [show z - x = -s - t by linarith]
    -- Reduce to proving a quadratic form is non-negative
    suffices A * s ^ 2 + (A - B + C) * s * t + C * t ^ 2 ≥ 0 by linarith
    -- Use the condition A² + B² + C² ≤ 2(AB + BC + CA) to show (A-B+C)² ≤ 4AC
    replace h : (A - B + C) ^ 2 ≤ 4 * A * C:= by linarith
    rw [show 4 * A * C = (2 * √(A * C)) ^ 2 by ring_nf ; field_simp ; ring_nf ; field_simp] at h
    replace h : |A - B + C| ≤ |2 * √(A * C)|:= by exact sq_le_sq.mp h
    rw [show |2 * √(A * C)| = 2 * √(A * C) by exact abs_of_nonneg (by positivity)] at h
    -- Complete the square to show the quadratic form is non-negative
    have h2 : (√A * |s| - √C * |t|) ^ 2 ≥ 0:= by positivity
    ring_nf at h2
    field_simp at h2
    rw [show -(√A * |s| * √C * |t| * 2) = -2 * √(A * C) * |s * t| by field_simp ; rw [show |s * t| = |s| * |t| by exact abs_mul s t] ; linarith] at h2
    have g1 : |s * t| ≥ 0:= by positivity
    replace g1 : 2 * √(A * C) * |s * t| ≥ |A - B + C| * |s * t|:= by exact mul_le_mul_of_nonneg_right h g1
    rw [show |A - B + C| * |s * t| = |(A - B + C) * (s * t)| by exact Eq.symm (abs_mul (A - B + C) (s * t))] at g1
    have g2 : |(A - B + C) * (s * t)| ≥ -((A - B + C) * (s * t)):= by exact neg_le_abs ((A - B + C) * (s * t))
    linarith

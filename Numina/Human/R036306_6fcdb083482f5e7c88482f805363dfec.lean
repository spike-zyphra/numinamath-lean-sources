import Mathlib

noncomputable def cubic_root (x : ℝ) : ℝ :=
  if 0 ≤ x
  then Real.rpow x (1 / 3)
  else - Real.rpow (- x) (1 / 3)

/- Find $f(x)$ such that $f(x)^{2} f((1-x) /(1+x))=64 x$ for $x$ not $0, \pm 1$. -/
theorem algebra_604783 {f : ℝ → ℝ} :
    (∀ x, x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 → (f x) ^ 2 * f ((1 - x) / (1 + x)) = 64 * x) ↔ (∀ x, x ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 → f x = 4 * cubic_root ((x ^ 2 * (1 + x)) / (1 - x))) := by
  -- Show a lemma that cubic_root is muliplicative.
  have cubic_root_mul (x y : ℝ) : cubic_root (x * y) = cubic_root x * cubic_root y := by
    simp [cubic_root, -one_div]
    -- Consider the cases 0 ≤ xy and xy < 0 respectively.
    split_ifs with hxy hy hx hx hy hx hx
    . rw [Real.mul_rpow hx hy]
    . have hy' : y ≤ 0 := by
        by_contra! hy'
        nlinarith
      simp [show y = 0 by linarith]
    . have hx' : x ≤ 0 := by
        by_contra! hx'
        nlinarith
      simp [show x = 0 by linarith]
    . rw [show x * y = (-x) * (-y) by ring, Real.mul_rpow (by linarith only [hx]) (by linarith only [hy]), neg_neg]
    . nlinarith
    . rw [show -(x * y) = (-x) * y by ring, Real.mul_rpow (by linarith only [hx]) hy]
    . rw [show -(x * y) = x * (-y) by ring, Real.mul_rpow hx (by linarith only [hy])]
    . nlinarith

  -- Split the goal into two parts.
  apply Iff.intro
  . -- Show that the given equation implies the specific form of f(x).
    intro h₀
    -- Substitute x = (1 - y) / (1 + y) into the original equation.
    have h₁ (y : ℝ) (h : y ≠ 0 ∧ y ≠ 1 ∧ y ≠ -1) : f ((1 - y) / (1 + y)) ^ 2 * f y = 64 * ((1 - y) / (1 + y)) := by
      -- Substitute x = (1 - y) / (1 + y) into the original equation.
      specialize h₀ ((1 - y) / (1 + y))
      -- Show that (1 - y) / (1 + y) ≠ 0.
      have h₁ : (1 - y) / (1 + y) ≠ 0 := by
        rw [div_ne_zero_iff, ne_eq, ne_eq, sub_eq_iff_eq_add', <-eq_sub_iff_add_eq]
        simp
        rw [<-ne_eq, <-ne_eq]
        simp [h.2.1.symm, <-neg_eq_iff_eq_neg, h.2.2.symm]
      simp [h₁] at h₀
      -- Show that (1 - y) / (1 + y) ≠ 1.
      have h₂ : (1 - y) / (1 + y) ≠ 1 := by
        by_contra! h₂
        rw [div_eq_iff] at h₂
        absurd h.1
        linarith only [h₂]
        by_contra! h₂
        absurd h.2.2
        linarith only [h₂]
      -- Show that (1 - y) / (1 + y) ≠ -1.
      have h₃ : (1 - y) / (1 + y) ≠ -1:= by
        by_contra! h₃
        rw [div_eq_iff] at h₃
        linarith only [h₃]
        by_contra! h₃
        absurd h.2.2
        linarith only [h₃]
      simp [h₂, h₃] at h₀
      clear h₂ h₃
      -- Simplify the expression using the substitution in h₀.
      rw [<-h₀]
      congrm ?_ * f ?_
      . rfl
      . field_simp [h.1, show 1 + y ≠ 0 by intro; absurd h.2.2; linarith]
        ring_nf
    -- Solve for f(x) combining h₀ and h₁.
    intro x hx
    specialize h₀ x hx
    specialize h₁ x hx
    replace h₀ : (f x ^ 2 * f ((1 - x) / (1 + x))) ^ 2 = (64 * x) ^ 2 := by
      rw [h₀]
    rw [mul_pow, show (f x ^ 2) ^ 2 = f x * f x ^ 3 by ring, mul_comm, <-mul_assoc, h₁, mul_comm] at h₀
    symm at h₀
    rw [<-div_eq_iff] at h₀
    symm at h₀
    rw [pow_two, mul_div_assoc, mul_div_mul_left _ _ (by norm_num), <-div_mul, mul_comm _ (1 + x), <-mul_div_assoc, mul_assoc, mul_div, show x * ((1 + x) * x) = x ^ 2 * (1 + x) by ring] at h₀
    -- Take cubic root of both sides to get the desired result.
    calc
      f x = cubic_root (f x ^ 3) := by
        simp [cubic_root, -one_div]
        -- Consider the cases 0 ≤ f(x)³ and f(x)³ < 0 respectively.
        split_ifs with hx
        . -- If 0 ≤ f(x)³, then 0 ≤ f(x).
          replace hx : 0 ≤ f x := by
            by_contra! hx'
            nlinarith only [hx, hx', show 0 < f x ^ 2 by nlinarith only [hx']]
          rw [<-Real.rpow_natCast, <-Real.rpow_mul hx]
          norm_num
        . -- If f(x)³ < 0, then f(x) < 0.
          replace hx : f x < 0 := by
            by_contra! hx'
            nlinarith only [hx, hx', sq_nonneg (f x)]
          rw [show -f x ^ 3 = (-f x) ^ 3 by ring]
          rw [<-Real.rpow_natCast, <-Real.rpow_mul (by linarith only [hx])]
          norm_num
      _ = cubic_root (64 * (x ^ 2 * (1 + x) / (1 - x))) := by
        rw [h₀]
      _ = 4 * cubic_root (x ^ 2 * (1 + x) / (1 - x)) := by
        -- Use the multiplicity of cubic_root.
        rw [cubic_root_mul]
        congrm ?_ * ?_
        . simp [cubic_root, -one_div]
          rw [show (64 : ℝ) = 4 ^ (3 : ℝ) by norm_cast, <-Real.rpow_mul (by norm_num)]
          norm_num
        . rfl
    -- Verify that 64 * ((1 - x) / (1 + x)) ≠ 0.
    simp [show 1 + x ≠ 0 by intro; absurd hx.2.2; linarith, show 1 - x ≠ 0 by intro; absurd hx.2.1; linarith]
  . -- Show that the specific form of f(x) satisfies the given equation.
    intro h₀
    intro x hx
    -- Substitute f(x) = 4 * cubic_root ((x ^ 2 * (1 + x)) / (1 - x)) into the original equation.
    rw [h₀ x hx]
    have hx' : (1 - x) / (1 + x) ≠ 0 ∧ (1 - x) / (1 + x) ≠ 1 ∧ (1 - x) / (1 + x) ≠ -1 := by
      refine ⟨?_, ?_, ?_⟩
      . rw [div_ne_zero_iff, ne_eq, ne_eq, sub_eq_iff_eq_add', <-eq_sub_iff_add_eq]
        simp
        rw [<-ne_eq, <-ne_eq]
        simp [hx.2.1.symm, <-neg_eq_iff_eq_neg, hx.2.2.symm]
      . by_contra! h₂
        rw [div_eq_iff] at h₂
        absurd hx.1
        linarith only [h₂]
        by_contra! h₂
        absurd hx.2.2
        linarith only [h₂]
      . by_contra! h₃
        rw [div_eq_iff] at h₃
        linarith only [h₃]
        by_contra! h₃
        absurd hx.2.2
        linarith only [h₃]
    rw [h₀ ((1 - x) / (1 + x)) hx']
    -- Use the multiplicity of cubic_root to simplify the expression.
    rw [mul_pow]
    nth_rewrite 2 [pow_two]
    rw [<-cubic_root_mul, <-pow_two, mul_comm (4 ^ 2), mul_comm, <-mul_assoc, mul_assoc 4, <-cubic_root_mul, mul_comm, <-mul_assoc]
    -- Show that x = cubic_root x³.
    have h₁ : x = cubic_root (x ^ 3) := by
      simp [cubic_root, -one_div]
      -- Consider the cases 0 ≤ x³ and x³ < 0 respectively.
      split_ifs with hx
      . -- If 0 ≤ x³, then 0 ≤ x.
        replace hx : 0 ≤ x := by
          by_contra! hx'
          nlinarith only [hx, hx', show 0 < x ^ 2 by nlinarith only [hx']]
        rw [<-Real.rpow_natCast, <-Real.rpow_mul hx]
        norm_num
      . -- If x³ < 0, then x < 0.
        replace hx : x < 0 := by
          by_contra! hx'
          nlinarith only [hx, hx', sq_nonneg x]
        rw [show -x ^ 3 = (-x) ^ 3 by ring]
        rw [<-Real.rpow_natCast, <-Real.rpow_mul (by linarith only [hx])]
        norm_num
    symm
    nth_rewrite 1 [h₁]
    congrm ?_ * cubic_root ?_
    . norm_num
    . field_simp [show 1 + x ≠ 0 by intro; absurd hx.2.2; linarith]
      rw [eq_div_iff]
      ring
      by_contra!
      simp [hx.1, show 1 + x ≠ 0 by intro; absurd hx.2.2; linarith, show 1 - x ≠ 0 by intro; absurd hx.2.1; linarith] at this

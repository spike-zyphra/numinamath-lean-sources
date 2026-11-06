import Mathlib


-- For the equation $x|x|+px+q=0$, which of the following conclusions is incorrect (    )?

-- A: There are at most three real roots;
-- B: There is at least one real root;
-- C: Real roots exist only when ${{p}^{2}}-4q \geqslant 0$;
-- D: When $p < 0$ and $q > 0$, there are three real roots.

theorem algebra_244035 :
  (∀ p q : ℝ, {x | x * |x| + p * x + q = 0}.encard ≤ 3 ∧ 1 ≤ {x | x * |x| + p * x + q = 0}.encard) ∧
  ¬ (∀ p q : ℝ, (1 ≤ {x | x * |x| + p * x + q = 0}.encard) → (p ^ 2 - 4 * q ≥ 0)) ∧
  ¬ (∀ p q : ℝ, p<0 → 0<q → {x | x * |x| + p * x + q = 0}.encard = 3) := by

  refine ⟨?_, ?_, ?_⟩
  . intro p q
    let S := {x | x * |x| + p * x + q = 0}
    suffices S.encard ≤ 3 ∧ 1 ≤ S.encard by unfold S at this; exact this
    rcases lt_trichotomy q 0 with hq | hq | hq
    . let x1 := -p/2 - √(p^2 - 4*q)/2
      let x2 := -p/2 + √(p^2 - 4*q)/2
      constructor
      . by_cases hq1 : p^2 + 4*q ≥ 0
        . let x3 := p/2 - √(p^2 + 4*q)/2
          let x4 := p/2 + √(p^2 + 4*q)/2
          have h1: S ⊆ ({x2, x3, x4}: Set ℝ) := by
            unfold S
            intro x hx
            simp at hx
            by_cases hx1 : 0 ≤ x
            . rw [abs_of_nonneg hx1] at hx
              have : (x-x1)*(x-x2) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith
              simp at this
              rcases this with h | h
              . have : x = x1 := by linarith
                rw [this] at hx1
                unfold x1 at hx1
                have : √(p ^ 2 - 4 * q) ≤ -p := by linarith
                rw [Real.sqrt_le_iff] at this
                linarith
              . left; linarith
            . simp at hx1
              rw [abs_of_neg hx1] at hx
              have : (-x+x3)*(x-x4) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith

              simp at this
              rcases this with h | h
              . right; left; linarith
              . right; right; simp; linarith
          apply Set.encard_mono at h1
          suffices ({x2, x3, x4}: Set ℝ).encard ≤ 3 by
            apply le_trans h1 this
          have h2 := Set.encard_insert_le ({x3, x4}: Set ℝ) x2
          have h3 := Set.encard_insert_le ({x4}: Set ℝ) x3
          replace h3 : ({x3, x4}: Set ℝ).encard + 1 ≤ 3 := by
            simp at h3
            exact add_le_add_right h3 1

          apply le_trans h2 h3

        . have : S ⊆ {x2} := by
            unfold S
            intro x hx
            simp at hx ⊢
            by_cases hx1 : 0 ≤ x
            . rw [abs_of_nonneg hx1] at hx
              have : (x-x1)*(x-x2) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith
              simp at this
              rcases this with h | h
              . have : x = x1 := by linarith
                rw [this] at hx1
                unfold x1 at hx1
                have : √(p ^ 2 - 4 * q) ≤ -p := by linarith
                rw [Real.sqrt_le_iff] at this
                linarith
              . linarith
            . simp at hx1 hq1
              rw [abs_of_neg hx1] at hx
              nlinarith [sq_nonneg (x-p/2)]

          apply Set.encard_mono at this
          simp at this
          apply le_trans this
          norm_num
      . simp
        use x2
        unfold S
        simp

        have : x2 > 0 := by
          suffices p < √(p^2 - 4*q) by
            unfold x2
            linarith
          apply Real.lt_sqrt_of_sq_lt
          linarith

        rw [abs_of_pos this]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        linarith

    . by_cases hp : 0 ≤ p
      . have : S = {0} := by
          unfold S
          rw [hq]
          ext x
          simp
          constructor
          . intro h
            have : x * (p + |x|) = 0 := by
              linarith
            simp at this
            rcases this with h | h
            . exact h
            . have : p = -|x| := by linarith
              rw [this] at hp
              have : |x| ≥ 0 := by positivity
              have : |x| = 0 := by linarith
              simp at this
              exact this

          . intro h
            rw [h]
            norm_num
        rw [this, Set.encard_singleton]
        norm_num
      . have : S = {-p, 0, p} := by
          unfold S
          rw [hq]
          ext x
          simp at hp ⊢
          constructor
          . intro h
            have : x * (p + |x|) = 0 := by
              linarith
            simp at this
            rcases this with h | h
            . right; left; exact h
            . have : |x| = -p := by linarith
              rw [abs_eq (by linarith)] at this
              rcases this with h | h
              . left; exact h
              . right; right; linarith [h]
          . intro h
            rcases h with rfl | rfl | rfl
            . rw [abs_of_pos (by linarith)]
              norm_num
            . norm_num
            . rw [abs_of_neg hp]
              norm_num
        by_cases hp0 : p = 0
        . rw [hp0] at this
          rw [this]
          simp
        . rw [this]
          simp
          have : -p ∉ ({0, p}: Set ℝ) := by
            simp
            refine ⟨hp0, ?_⟩
            by_contra
            linarith
          rw [Set.encard_insert_of_not_mem this]
          rw [Set.encard_pair (Ne.symm hp0)]
          norm_num

    . let x3 := p/2 - √(p^2 + 4*q)/2
      let x4 := p/2 + √(p^2 + 4*q)/2
      constructor
      . by_cases hq1 : p^2 - 4*q ≥ 0
        . let x1 := -p/2 - √(p^2 - 4*q)/2
          let x2 := -p/2 + √(p^2 - 4*q)/2
          have h1: S ⊆ ({x1, x2, x3}: Set ℝ) := by
            unfold S
            intro x hx
            simp at hx
            by_cases hx1 : 0 < x
            . rw [abs_of_pos hx1] at hx
              have : (x-x1)*(x-x2) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith
              simp at this
              rcases this with h | h
              . left; linarith
              . right; left; linarith
            . simp at hx1
              rw [abs_of_nonpos hx1] at hx
              have : (-x+x3)*(x-x4) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith
              simp at this
              rcases this with h | h
              . right; right; simp; linarith
              . have : x = x4 := by linarith
                rw [this] at hx1
                unfold x4 at hx1
                have : √(p ^ 2 + 4 * q) ≤ -p := by linarith
                rw [Real.sqrt_le_iff] at this
                linarith

          apply Set.encard_mono at h1
          suffices ({x1, x2, x3}: Set ℝ).encard ≤ 3 by
            apply le_trans h1 this
          have h2 := Set.encard_insert_le ({x2, x3}: Set ℝ) x1
          have h3 := Set.encard_insert_le ({x3}: Set ℝ) x2
          replace h3 : ({x2, x3}: Set ℝ).encard + 1 ≤ 3 := by
            simp at h3
            apply add_le_add_right h3 1
          apply le_trans h2 h3
        . have : S ⊆ {x3} := by
            unfold S
            intro x hx
            simp at hx ⊢
            by_cases hx1 : 0 < x
            . rw [abs_of_pos hx1] at hx
              nlinarith [sq_nonneg (x+p/2)]
            . simp at hx1
              rw [abs_of_nonpos hx1] at hx
              have : (-x+x3)*(x-x4) = 0 := by
                rw [← hx]
                ring_nf
                rw [Real.sq_sqrt (by nlinarith)]
                linarith
              simp at this
              rcases this with h | h
              . linarith [h]
              . have : x = x4 := by linarith
                rw [this] at hx1
                unfold x4 at hx1
                have : √(p ^ 2 + 4 * q) ≤ -p := by linarith
                rw [Real.sqrt_le_iff] at this
                linarith

          apply Set.encard_mono at this
          simp at this
          apply le_trans this
          norm_num
      . simp
        use x3
        unfold S
        simp
        have : x3 < 0 := by
          suffices p < √(p^2 + 4*q) by
            unfold x3
            linarith
          apply Real.lt_sqrt_of_sq_lt
          linarith

        rw [abs_of_neg this]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        linarith

  . simp
    use 1, 1
    simp
    use 1/2 - √5/2
    simp
    have : 2⁻¹ - √5 / 2 < 0 := by
      have : 1 < √5 := by
        rw [Real.lt_sqrt]
        . norm_num
        . norm_num
      linarith
    rw [abs_of_neg this]
    ring_nf
    rw [Real.sq_sqrt (by norm_num)]
    linarith

  . simp
    use -1
    simp
    use 1
    simp
    have : {x | x * |x| + -x + 1 = 0} = {-1/2-√5/2} := by
      ext x
      simp
      constructor
      . intro h
        by_cases hx : 0 ≤ x
        . rw [abs_of_nonneg hx] at h
          nlinarith [sq_nonneg (x-1/2)]
        . simp at hx
          rw [abs_of_neg hx] at h
          have : (x-(-1/2-√5/2))*(-x-1/2+√5/2) = 0 := by
            rw [← h]
            ring_nf
            rw [Real.sq_sqrt (by norm_num)]
            linarith
          simp at this
          rcases this with h | h
          . linarith
          . have : x = - 2⁻¹ + √5 / 2 := by linarith [h]
            rw [this] at hx
            have : √5 < 2 := by linarith [hx]
            rw [Real.sqrt_lt (by norm_num) (by norm_num)] at this
            norm_num at this

      . intro h
        rw [h]
        have : -1 / 2 - √5 / 2 < 0 := by
          have : √5 > 0 := by positivity
          linarith
        rw [abs_of_neg this]
        ring_nf
        rw [Real.sq_sqrt (by norm_num)]
        linarith
    rw [this]
    simp

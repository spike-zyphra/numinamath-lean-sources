import Mathlib

open Real Set

/--If the equation log kx=2*log(x+1) has only one real root, then the range of values for k is 
-/
theorem algebra_242407 (k : ℝ) :
    (∃!x : ℝ, 0 < k * x ∧ 0 < x + 1 ∧ logb 10 (k * x) = 2 * logb 10 (x + 1)) ↔ k < 0 ∨ k = 4 := by
  constructor
  --if there exists a unique x so that logb 10 (k * x) = 2 * logb 10 (x + 1), then k < 0 andd k = 4
  · intro h
    obtain ⟨x, ⟨hx1, hx2, hx3⟩, hx4⟩ := h
    simp at hx4
    --take the corresponding quadratic equation coming from equating the arguments of the logarithms
    have eq3 : 1 * (x * x) + (2 - k) * x + 1 = 0 := by
      rw[(by norm_cast : (2 : ℝ) = (2 : ℕ)), ← logb_pow 10] at hx3 
      have := @Real.logb_injOn_pos 10 (by linarith)
      specialize @this (k * x) hx1 ((x + 1) ^ 2) (sq_pos_of_pos hx2) hx3
      ring_nf at this
      linarith
    --solving the equation with the resolution formula, yields a discriminant of k*(k-4), which allows for solution if and only if is positive
    --i.e. when k ≤ 0 or k ≥ 4
    have hk_tot : k ≤ 0 ∨ k ≥ 4 := by
      have Δeq := discrim_eq_sq_of_quadratic_eq_zero eq3 
      have Δnonneg : discrim 1 (2 - k) 1 ≥ 0 := by 
        rw[Δeq]
        exact sq_nonneg (2 * 1 * x + (2 - k))
      unfold discrim at Δnonneg
      have discrim_mul_nonneg : 0 ≤ k * (k - 4) := by ring_nf; linarith
      rw[mul_nonneg_iff] at discrim_mul_nonneg
      simp at discrim_mul_nonneg
      obtain opt1|opt2 := discrim_mul_nonneg
      · right
        linarith
      · left
        linarith
    obtain hk1|hk2 := hk_tot
    --the case when k < 0 is exactly what we want
    · by_cases hklt0 : k < 0
      · left
        exact hklt0
      --k = 0, which can never happen since kx > 0
      · have hk0 : k = 0 := by linarith
        rw[hk0] at hx1
        exfalso
        simp at hx1
    --the case k = 4 is again exactly what we want
    · by_cases hk4 : k = 4
      · right
        exact hk4
      --we have to exclude now the case k > 4
      · have hkgt4 : k > 4 := by exact lt_of_le_of_ne hk2 (id (Ne.symm hk4))
        have eq' : x * x - (k - 2) * x + 1 = 0 := by linarith
        --by vieta formula we have that given the root x, the other root y is so that xy = 1 and x+y = k-2
        have vieta := vieta_formula_quadratic eq'
        obtain ⟨y, hy1, hy2, hy3⟩ := vieta
        --x must be positive since kx>0
        have xpos : x > 0 := by 
          rw[mul_pos_iff] at hx1
          obtain hx11|hx12 := hx1
          · exact hx11.2
          · exfalso; linarith
        --y must also be positive since xy=1
        have ypos : y > 0 := by 
          by_contra hynonpos
          push_neg at hynonpos
          have : x * y ≤ 0 := by exact mul_nonpos_iff.2 (by left; exact ⟨le_of_lt xpos, hynonpos⟩)
          linarith
        --then y fulfills also the logarithmic equation corresponding to the quadratic one
        have y_fullfils_log_eq : logb 10 (k * y) = 2 * logb 10 (y + 1) := by 
          have : k * y = (y + 1) ^ 2 := by ring_nf; linarith
          rw[this, logb_pow 10]
          simp 
        specialize hx4 y (mul_pos_iff.2 (by left; exact ⟨by linarith, ypos⟩)) (by linarith) y_fullfils_log_eq
        rw[hx4] at hy3
        --in this case we have two possibilities x = 1 and x = -1
        have eq_mul : (x - 1) * (x + 1) = 0 := by ring_nf; linarith
        rw[mul_eq_zero] at eq_mul
        obtain root1|root2 := eq_mul
        --the first case is false since by substituting the equality fails
        · have xis1: x = 1 := by linarith
          rw[xis1] at eq3
          exfalso
          linarith 
        --the second case is false because we had x > 0
        · exfalso
          linarith
  --now assume k < 0 and k = 4, we prove that there exist a unique x so that the logarithmic equality holds
  · intro h
    obtain hklt0|hk4 := h
    --in the first case k < 0
    · let s := sqrt (discrim 1 (2 - k) 1)
      have hs : discrim 1 (2 - k) 1 = s * s := by 
        simp[s]
        rw[← sq, Real.sq_sqrt (by simp[discrim]; rw[sq, (by norm_num : (4 : ℝ) = 2 * 2)]; exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))] 
      --it suffices to show that there exists a root for the quadratic equation
      suffices ∃ x, 1 * (x * x) + (2 - k) * x + 1 = 0 by
        obtain ⟨x, hx⟩ := this
        by_cases boundx : x ≤ -1
        --in fact if we assume it exists in cannot be -1 since it would give falso
        · by_cases hxmone : x = -1
          · rw[hxmone] at hx
            exfalso
            linarith
          --if we assume x < -1 by vieta formula we obtain the root y so that xy=1 and x+y=k-2
          · have eqx' : x * x - (k - 2) * x + 1 = 0 := by linarith 
            have vieta := vieta_formula_quadratic eqx'
            obtain ⟨y, hy, hy1, hy2⟩ := vieta
            use y
            simp
            -- y is greater than -1 since xy=1 this gives us y+1>0 the second condition
            have : -1 < y := by 
              by_contra hh
              push_neg at hh
              rw[← mul_le_mul_left_of_neg (LT.lt.trans (lt_of_le_of_ne boundx hxmone) (by linarith))] at hh
              rw[hy2, ← neg_le_neg_iff] at hh
              norm_num at hh
              have : x = -1 := by linarith
              contradiction
            constructor
            --y is less than 0 because x is less than 0 and xy is positive, this gives us ky>0 the first condition
            · have yneg : y < 0 := by
                by_contra ynonneg
                have mul_pos : x * y > 0 := by linarith
                have xneg : x < 0 := by linarith
                push_neg at ynonneg
                have mul_nonpos : x * y ≤ 0 := by exact mul_nonpos_iff.2 (by right; exact ⟨le_of_lt xneg, ynonneg⟩)
                linarith
              have := (@mul_pos_iff _ _ _ x y _ _ _ _ _).1 (by linarith)
              obtain case1|case2 := this
              · have : x + y < 0 := by linarith
                exfalso
                linarith
              --and y fullfils the logarithmic equation because corresponds to the quadratic one
              · constructor
                · exact mul_pos_iff.2 (by right; exact ⟨hklt0, yneg⟩)
                · constructor
                  · linarith
                  · have equal : k * y = (y + 1) ^ 2 := by ring_nf; linarith
                    rw[equal, logb_pow 10]
                    simp
            --y is unique with those properties because if taken another z with those, then either z = x or z = y
            --if z = y we are done, if z = x then z + 1 < 0 contraddiction the required z + 1 > 0
            · intro z hz1 hz2 hzeq
              have quadratic_z : 1 * (z * z) + (2 - k) * z + 1 = 0 := by 
                rw[(by norm_cast : (2 : ℝ) = (2 : ℕ)), ← logb_pow 10] at hzeq
                have := @Real.logb_injOn_pos 10 (by linarith)
                specialize @this (k * z) hz1 ((z + 1) ^ 2) (sq_pos_of_pos hz2) hzeq
                ring_nf at this
                linarith
              have quadratic_x : 1 * (x * x) + (2 - k) * x + 1 = 0 := by linarith
              have quadratic_y : 1 * (y * y) + (2 - k) * y + 1 = 0 := by linarith
              rw[quadratic_eq_zero_iff (one_ne_zero) hs y] at quadratic_y
              rw[quadratic_eq_zero_iff (one_ne_zero) hs z] at quadratic_z
              rw[quadratic_eq_zero_iff (one_ne_zero) hs x] at quadratic_x
              have xnez : y ≠ x := by linarith
              have ynez : z ≠ x := by linarith
              have eqeq : x = z ∨ x = y ∨ y = z := by 
                obtain x1|x2 := quadratic_x
                · obtain y1|y2 := quadratic_y
                  · obtain z1|z2 := quadratic_z
                    · rw[← y1] at x1; right; left; exact x1
                    · rw[← y1] at x1; right; left; exact x1
                  · obtain z1|z2 := quadratic_z
                    · rw[← z1] at x1; left; exact x1
                    · rw[← z2] at y2; right; right; exact y2
                · obtain y1|y2 := quadratic_y
                  · obtain z1|z2 := quadratic_z
                    · rw[← z1] at y1; right; right; exact y1
                    · rw[← z2] at x2; left; exact x2
                  · obtain z1|z2 := quadratic_z
                    · rw[← y2] at x2; right; left; exact x2
                    · rw[← z2] at y2; right; right; exact y2
              obtain eq1|eq2|eq3 := eqeq
              · exfalso
                linarith
              · exfalso
                linarith
              · exact (symm eq3)
        --on the countrary if -1 < x, we use x directly and proceed with the same method as above
        · push_neg at boundx
          use x
          simp
          constructor
          · have eqx' : x * x - (k - 2) * x + 1 = 0 := by linarith 
            have vieta := vieta_formula_quadratic eqx'
            obtain ⟨y, hy, hy1, hy2⟩ := vieta
            have xneg : x < 0 := by 
              have := (@mul_pos_iff _ _ _ x y _ _ _ _ _).1 (by linarith)
              obtain case1|case2 := this
              · have : x + y < 0 := by linarith
                exfalso
                linarith
              · exact case2.1
            constructor
            · exact mul_pos_iff.2 (by right; exact ⟨hklt0, xneg⟩)
            · constructor
              · linarith
              · have equal : k * x = (x + 1) ^ 2 := by ring_nf; linarith
                rw[equal, logb_pow 10]
                simp
          · intro y hy1 hy2 hyeq
            have eqx' : x * x - (k - 2) * x + 1 = 0 := by linarith 
            have vieta := vieta_formula_quadratic eqx'
            obtain ⟨z, hzeq, hz1, hz2⟩ := vieta
            have z_lt_mone : z < -1 := by 
              by_contra hh
              push_neg at hh
              have sum_neg: x + z < 0 := by linarith
              have := (@mul_pos_iff _ _ _ x z _ _ _ _ _).1 (by linarith)
              obtain case1|case2 := this
              · exfalso
                linarith
              · rw[← mul_lt_mul_right_of_neg (LT.lt.trans (by linarith) case2.2)] at boundx
                rw[hz2, ← neg_lt_neg_iff] at boundx
                norm_num at boundx
                linarith
            have quadratic_y : 1 * (y * y) + (2 - k) * y + 1 = 0 := by 
              rw[(by norm_cast : (2 : ℝ) = (2 : ℕ)), ← logb_pow 10] at hyeq
              have := @Real.logb_injOn_pos 10 (by linarith)
              specialize @this (k * y) hy1 ((y + 1) ^ 2) (sq_pos_of_pos hy2) hyeq
              ring_nf at this
              linarith
            have quadratic_z : 1 * (z * z) + (2 - k) * z + 1 = 0 := by linarith
            rw[quadratic_eq_zero_iff (one_ne_zero) hs x] at hx
            rw[quadratic_eq_zero_iff (one_ne_zero) hs y] at quadratic_y
            rw[quadratic_eq_zero_iff (one_ne_zero) hs z] at quadratic_z
            have xnez : x ≠ z := by linarith
            have ynez : y ≠ z := by linarith
            have eqeq : x = z ∨ x = y ∨ y = z := by 
              obtain x1|x2 := hx
              · obtain y1|y2 := quadratic_y
                · obtain z1|z2 := quadratic_z
                  · rw[← y1] at x1; right; left; exact x1
                  · rw[← y1] at x1; right; left; exact x1
                · obtain z1|z2 := quadratic_z
                  · rw[← z1] at x1; left; exact x1
                  · rw[← z2] at y2; right; right; exact y2
              · obtain y1|y2 := quadratic_y
                · obtain z1|z2 := quadratic_z
                  · rw[← z1] at y1; right; right; exact y1
                  · rw[← z2] at x2; left; exact x2
                · obtain z1|z2 := quadratic_z
                  · rw[← y2] at x2; right; left; exact x2
                  · rw[← z2] at y2; right; right; exact y2
            obtain eq1|eq2|eq3 := eqeq
            · exfalso
              linarith
            · exact (symm eq2)
            · exfalso
              linarith
      --a root to the quadratic equation exists because the discriminant has a root
      exact exists_quadratic_eq_zero one_ne_zero (by use s)
    --in the case k = 4 we use the root 1 which is the unique root since (x-1)^2 = 0 is the corresponding quadratic equation to the logarithmic one
    · use 1
      simp
      constructor
      · exact ⟨by linarith, by rw[hk4, (by norm_cast : (2 : ℝ) = (2 : ℕ)), ← logb_pow 10]; norm_num⟩ 
      · intro y hy hygt1 hysol
        rw[hk4, (by norm_cast : (2 : ℝ) = (2 : ℕ)), ← logb_pow 10] at hysol
        have := @Real.logb_injOn_pos 10 (by linarith)
        unfold InjOn at this
        rw[hk4] at hy
        simp at this
        specialize @this (4 * y) hy ((y + 1) ^ 2) (sq_pos_of_pos hygt1) hysol
        have eq : (y - 1) * (y - 1) = 0 := by ring_nf at this; linarith
        rw[mul_eq_zero] at eq
        simp at eq
        linarith
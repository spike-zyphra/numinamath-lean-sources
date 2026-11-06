import Mathlib

/- Example 13 Let $a, b, c \in \mathbf{R}^{+}$, prove:
(1) $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b} \geqslant \frac{3}{2}$;
(2) $a^{3}+b^{3}+c^{3}+\frac{1}{a}+\frac{1}{b}+\frac{1}{c} \geqslant 2(a+b+c)$. -/

theorem inequalities_127194 (a b c : ℝ) (ha : 0 < a) 
      (hb : 0 < b) (hc : 0 < c) :
  3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
  a^3 + b^3 + c^3 + 1 / a + 1 / b + 1 / c ≥ 2 * (a + b + c) := by 
  apply And.intro
  -- Define the abbreviations S M N
  · set S := a / (b + c) + b / (c + a) + c / (a + b)
    set M := b / (b + c) + c / (c + a) + a / (a + b)
    set N := c / (b + c) + a / (c + a) + b / (a + b)
    -- Simple result about M and N
    have m_plus_n : M + N = 3 := by 
      unfold M N
      have : b/(b + c) + c/(c + a) + a/(a + b) +
       (c/(b + c) + a/(c + a) + b/(a + b)) =
(b/(b + c) + c/(b + c)) + (c/(c + a) + a/(c + a)) + (a/(a + b) + b/(a + b)) := by ac_rfl
      rw [this]
      repeat rw [← add_div]
      field_simp
      ring
    -- Key inequality proved using the AM>GM inequality
    have m_plus_s : 3 ≤ M + S := by 
      unfold M S
      -- use the Arithmetic Geometric Mean to show a useful result
      have m_plus_s: b/(b + c) + c/(c + a) + a/(a + b) +
       (a/(b + c) + b/(c + a) + c/(a + b)) =
(a/(b + c) + b/(b + c)) + (b/(c + a) + c/(c + a)) + (c/(a + b) + a/(a + b)) := by ac_rfl
      rw [m_plus_s] 
      repeat rw [← add_div]
      set x1 := (a + b) / (b + c)
      set x2 := (b + c) / (c + a)
      set x3 := (c + a) / (a + b)
      have one_third: 0 ≤ (1/3: ℝ) := by linarith
      have x1nonneg: 0 ≤ x1 := by 
        unfold x1
        have den: b + c > 0 := by linarith
        have num: a + b > 0 := by linarith
        have : (a + b) / (b + c) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x2nonneg: 0 ≤ x2 := by 
        unfold x2
        have den: b + c > 0 := by linarith
        have num: c + a > 0 := by linarith
        have : (b + c) / (c + a) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x3nonneg: 0 ≤ x3 := by 
        unfold x3
        have den: c + a > 0 := by linarith
        have num: a + b > 0 := by linarith
        have : (c + a) / (a + b) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x123: x1*x2*x3 = 1 := by 
        unfold x1 x2 x3
        have step1 : (a + b) / (b + c) * ((b + c) / (c + a)) * ((c + a) / (a + b)) = 
        (a + b)/(a + b)*((b + c)/(b + c))*((c + a) / (c + a)) := by field_simp
        rw [step1, div_self, div_self, div_self, one_mul, one_mul]
        all_goals try linarith
      have gm_am_ineq := Real.geom_mean_le_arith_mean3_weighted one_third one_third 
           one_third x1nonneg x2nonneg x3nonneg (by linarith)
      rw [← Real.mul_rpow, ← Real.mul_rpow, x123, Real.one_rpow] at gm_am_ineq
      cancel_denoms at gm_am_ineq
      exact gm_am_ineq
      exact mul_nonneg x1nonneg x2nonneg
      repeat assumption
    -- similar to m_plus_s
    have n_plus_s : 3 ≤ N + S := by 
      unfold N S
      -- use the Arithmetic Geometric Mean to show a useful result
      have n_plus_s': c/(b + c) + a/(c + a) + b/(a + b) +
       (a/(b + c) + b/(c + a) + c/(a + b)) =
(c/(b + c) + a/(b + c)) + (a/(c + a) + b/(c + a)) + (b/(a + b) + c/(a + b)) := by ac_rfl
      rw [n_plus_s'] 
      repeat rw [← add_div]
      set x1 := (c + a) / (b + c)
      set x2 := (a + b) / (c + a)
      set x3 := (b + c) / (a + b)
      have one_third: 0 ≤ (1/3: ℝ) := by linarith
      have x1nonneg: 0 ≤ x1 := by 
        unfold x1
        have den: b + c > 0 := by linarith
        have num: c + a > 0 := by linarith
        have : (c + a) / (b + c) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x2nonneg: 0 ≤ x2 := by 
        unfold x2
        have den: c + a > 0 := by linarith
        have num: a + b > 0 := by linarith
        have : (a + b) / (c + a) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x3nonneg: 0 ≤ x3 := by 
        unfold x3
        have den: a + b > 0 := by linarith
        have num: b + c > 0 := by linarith
        have : (b + c) / (a + b) > 0 := by 
          simp_all only [div_pos_iff_of_pos_left]
        exact le_of_lt this
      have x123: x1*x2*x3 = 1 := by 
        unfold x1 x2 x3
        have step1 : (c + a) / (b + c) * ((a + b) / (c + a)) * ((b + c) / (a + b)) = 
        (a + b)/(a + b)*((b + c)/(b + c))*((c + a) / (c + a)) := by 
          field_simp
          ring
        rw [step1, div_self, div_self, div_self, one_mul, one_mul]
        all_goals try linarith
      have gm_am_ineq := Real.geom_mean_le_arith_mean3_weighted one_third one_third 
           one_third x1nonneg x2nonneg x3nonneg (by linarith)
      rw [← Real.mul_rpow, ← Real.mul_rpow, x123, Real.one_rpow] at gm_am_ineq
      cancel_denoms at gm_am_ineq
      --unfold x1 x2 x3 at gm_am_ineq
      exact gm_am_ineq
      exact mul_nonneg x1nonneg x2nonneg
      repeat assumption
    -- add both previous inequalities
    have mn_plus_s: 6 ≤ M + N + 2*S := by
      have both_plus:= add_le_add m_plus_s n_plus_s
      norm_num at both_plus
      have: M + S + (N + S) = M + N + 2*S := by ring
      rw [this] at both_plus
      exact both_plus
    rw [m_plus_n] at mn_plus_s
    cancel_denoms
    unfold S at mn_plus_s
    linarith [mn_plus_s]
  · have x_1x_ineq:  ∀ x:ℝ , x>0 → x^3 + 1/x ≥ 2*x := by 
    -- This inequality will be used three times to show the main result
      intro x hx
      have invx: 1/x > 0 := by 
        have := (inv_pos.2 hx)
        rw [← one_div] at this
        exact this
      have one_half: 0 ≤ (1/2: ℝ) := by linarith
      have cub_nneg: 0 ≤ x^(3: ℝ ) := by 
        exact le_of_lt (Real.rpow_pos_of_pos hx 3)
      have gm_am_ineq := Real.geom_mean_le_arith_mean2_weighted  one_half 
             one_half (cub_nneg) (le_of_lt invx) (by field_simp)
      have xnonzero : x ≠ 0 := by linarith 
      rw [← Real.mul_rpow, mul_one_div, ← Real.rpow_sub_one ] at gm_am_ineq
      ring_nf at gm_am_ineq
      rw [← Real.rpow_mul] at gm_am_ineq
      ring_nf at gm_am_ineq
      rw [Real.rpow_one] at gm_am_ineq
      cancel_denoms at gm_am_ineq
      rw [ge_iff_le, one_div, ← Real.rpow_natCast]
      exact gm_am_ineq
      all_goals try linarith
    -- Add the inequalities resulting from a and b
    have a_plus_b := add_le_add (x_1x_ineq a ha) (x_1x_ineq b hb) 
    -- Then add the inequality corresponding to c
    have abc_plus := add_le_add a_plus_b (x_1x_ineq c hc)
    norm_num at abc_plus
    rw [ge_iff_le]
    ring_nf at abc_plus
    ring_nf
    exact abc_plus
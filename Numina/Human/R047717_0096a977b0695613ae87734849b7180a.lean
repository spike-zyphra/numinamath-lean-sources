import Mathlib

/- Subject 2. Let $a, b, c, n>0$ with $a+b+c=1$. Prove the inequality:


$$

\frac{a}{b c(b+n c)}+\frac{b}{c a(c+n a)}+\frac{c}{a b(a+n b)} \geq \frac{27}{n+1}

$$
 -/
theorem inequalities_118955 (a b c n : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hn : 0 < n)
    (h : a + b + c = 1) :
    27 / (n + 1) ≤ a / (b * c * (b + n * c)) + b / (c * a * (c + n * a)) +
    c / (a * b * (a + n * b)) := by

      -- We use AM-GM to get upper bound of `a * b * c`
      have le_one : a*b*c ≤ ((a + b + c) / 3) ^ (3 : ℝ) := by
        have yeahh := Real.geom_mean_le_arith_mean Finset.univ (fun x: Fin 3 => 1) (![a, b, c]) ?_ ?_ ?_
        have prod_eq : (∏ x : Fin 3, ![a, b, c] x) = a * b * c
          := Fin.prod_univ_three ![a, b, c]
        have sum_eq := Fin.sum_univ_three ![a, b, c]
        simp [prod_eq, sum_eq] at yeahh
        suffices h : ((a * b * c) ^ (3⁻¹ : ℝ)) ^ (3 : ℝ) ≤ ((a + b + c) / 3) ^ (3 : ℝ)
        · rw [Real.rpow_inv_rpow] at h
          exact h
          positivity
          linarith
        refine (Real.rpow_le_rpow_iff ?_ ?_ ?_).mpr yeahh <;> positivity
        simp only [Finset.mem_univ, zero_le_one, imp_self, implies_true]
        positivity
        simp only [Finset.mem_univ, forall_const]
        intro i
        fin_cases i <;> { simp ; positivity }

      -- Which means that `27 ≤ 1 / (a * b * c)`
      have const_upper : a * b * c ≤ (1 / 27 : ℝ)
        := le_trans le_one <| le_of_eq (h.symm ▸ (by ring))
      have const_upper' : 1 / (1 / 27 : ℝ) ≤ 1 / (a * b * c)
        := one_div_le_one_div_of_le (by positivity) const_upper
      have const_upper'' : 27 ≤ 1 / (a * b * c)
        := le_trans (le_of_eq (one_div_one_div 27).symm) const_upper'

      -- Chain relations
      calc 27 / (n + 1)
      -- Use bound proved above
      _ ≤ (1 / (a * b * c)) / (n + 1)
        := (div_le_div_iff_of_pos_right (by positivity)).mpr const_upper''
      _ = 1 / (a * b * c * (n + 1))
        := (div_mul_eq_div_div 1 (a * b * c) (n + 1)).symm
      _ = (a + b + c) ^ 2 / (a * b * c * (a + b + c) * (n + 1)) := by
        simp only [one_div, mul_inv_rev, h, one_pow, mul_one]
      -- Use Titu's lemma / Sedrakyan's inequality
      _ ≤ a ^ 2 / (a * (b * c * (b + n * c))) + b ^ 2 / (b * (c * a * (c + n * a))) + c ^ 2 / (c * (a * b * (a + n * b))) := by
        have titu := @Finset.sq_sum_div_le_sum_sq_div _ _ _ _ Finset.univ ![a, b, c]
          ![(a * (b * c * (b + n * c))), (b * (c * a * (c + n * a))), (c * (a * b * (a + n * b)))]
          ?_
        simp only [Fin.sum_univ_three, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at titu
        refine le_trans (le_of_eq ?_) titu
        · congr
          ring
        · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Finset.mem_univ, forall_const]
          intro i
          fin_cases i
          · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
            positivity
          · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
            positivity
          · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Nat.succ_eq_add_one, Nat.reduceAdd,
              Matrix.tail_cons, Matrix.head_cons]
            positivity
      -- Then we're done
      _ = a / (b * c * (b + n * c)) + b / (c * a * (c + n * a)) + c / (a * b * (a + n * b)) := by
        congr 1
        congr 1
        all_goals
        · rw [pow_two]
          exact mul_div_mul_left _ _ (by positivity)
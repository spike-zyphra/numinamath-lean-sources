import Mathlib

/- ## Task 14/79

Prove: If $a, b, c$ are the side lengths of any triangle, then the inequality chain


$$

\frac{3}{2} \leq \frac{a}{b+c}+\frac{b}{a+c}+\frac{c}{a+b}<3

$$


holds. -/

theorem inequalities_157656 (a b c : ℝ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h :  c < a + b) (h' : b < a + c) (h'' : a < b + c) :
  3 / 2 ≤ a / (b + c) + b / (a + c) + c / (a + b) ∧
  a / (b + c) + b / (a + c) + c / (a + b) < 3
  := by
    -- We first show the lower bound, then the upper bound
    refine ⟨?_, ?_⟩
    · -- We'll use the arithmetic and harmonic means inequality on (a + b), (b + c) and (c + a).
      let values : Fin 3 → ℝ := ![(a + b), (b + c), (c + a)]
      have values_lt_zero : ∀ i ∈ Finset.univ, 0 < values i
      · simp only [Finset.mem_univ, forall_const]
        intro i
        unfold values
        fin_cases i
        all_goals
        · simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
          Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.head_cons]
          positivity

      have values_le_zero : (∀ i ∈ Finset.univ, 0 ≤ values i)
        := fun i ih => le_of_lt <| values_lt_zero i ih

      -- We use the weighted version with all weights equal, i.e. the unweighted version
      have weights_lt_zero : ∀ i : Fin 3, i ∈ Finset.univ → 0 < 1 / (3 : ℝ)
      · simp only [Finset.mem_univ, forall_const]
        linarith

      have weights_le_zero : ∀ i : Fin 3, i ∈ Finset.univ → 0 ≤ 1 / (3 : ℝ)
        := fun i ih => le_of_lt <| weights_lt_zero i ih
      have weights_eq_one : ∑ i : Fin 3, (1 / 3) = (1 : ℝ)
      · rw [Fin.sum_const]
        simp only [one_div, nsmul_eq_mul, Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel]

      -- We chain together the AM-GM inequality and HM-GM inequality
      have am_gm := Real.geom_mean_le_arith_mean_weighted Finset.univ
        (fun x => (1 / 3)) values weights_le_zero weights_eq_one values_le_zero
      have hm_gm := Real.harm_mean_le_geom_mean_weighted Finset.univ (fun x => (1 / 3))
        values Finset.univ_nonempty weights_lt_zero weights_eq_one values_lt_zero
      have hm_am := le_trans hm_gm am_gm
      unfold values at hm_am

      -- Simplify
      simp only [Finset.sum, one_div, Fin.univ_val_map, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero,
        Matrix.cons_val_succ, Matrix.cons_val_fin_one, List.ofFn_zero, Multiset.sum_coe,
        List.sum_cons, List.sum_nil, add_zero] at hm_am
      ring_nf at hm_am
      simp only [←add_mul, mul_inv, one_div, inv_inv] at hm_am

      -- We do equivalent transformations of the hm_am inequality
      have main_le := mul_le_mul hm_am (le_refl <| ((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) * 3⁻¹) (by positivity) (by positivity)

      -- Simplify the left hand side
      have ls : ((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹)⁻¹ * 3 * (((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) * 3⁻¹) = 1
      · nth_rw 2 [mul_comm]
        rw [mul_assoc]
        nth_rw 2 [←mul_assoc]
        nth_rw 3 [mul_comm]
        have yep : ((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) ≠ 0 := by positivity
        rw [(mul_inv_eq_one₀ yep).mpr rfl]
        ring_nf

      rw [ls] at main_le

      -- Simplify the right hand side
      have rs : (a + b + c) * (2 / 3) * (((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) * 3⁻¹)
        = (2 / 9) * (1 + c / (a + b) + 1 + a / (b + c) + 1 + b / (a + c))
      · calc (a + b + c) * (2 / 3) * (((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) * 3⁻¹)
        _ = (a + b + c) * (2 / 9) * ((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) := by ring_nf
        _ = (2 / 9) * (a + b + c) * ((a + b)⁻¹ + (b + c)⁻¹ + (a + c)⁻¹) := by ring_nf
        _ = (2 / 9) * ((a + b + c)*(a + b)⁻¹ + (a + b + c)*(b + c)⁻¹ + (a + b + c)*(a + c)⁻¹) := by ring_nf
        _ = (2 / 9) * ((1 + c / (a + b)) + (1 + a / (b + c)) + (1 + b / (a + c))) := by
          congr 3
          · ring_nf
            have ne_zero : (a + b) ≠ 0 := by positivity
            rw [add_left_inj, ←add_mul, (mul_inv_eq_one₀ ne_zero).mpr rfl]
          · ring_nf
            have ne_zero : (b + c) ≠ 0 := by positivity
            rw [add_assoc, add_comm, add_left_inj, ←add_mul, (mul_inv_eq_one₀ ne_zero).mpr rfl]
          · ring_nf
            have ne_zero : (a + c) ≠ 0 := by positivity
            rw [add_assoc]
            nth_rw 3 [add_comm]
            rw [←add_assoc, add_left_inj, ←add_mul, (mul_inv_eq_one₀ ne_zero).mpr rfl]

        _ = (2 / 9) * (1 + c / (a + b) + 1 + a / (b + c) + 1 + b / (a + c)) := by ring_nf

      rw [rs] at main_le

      -- Seperate out constants
      have fin : (2 / 9) * (1 + c / (a + b) + 1 + a / (b + c) + 1 + b / (a + c))
        = (2 / 3) + (2 / 9) * (a / (b + c) + b / (a + c) + c / (a + b))
      · calc (2 / 9) * (1 + c / (a + b) + 1 + a / (b + c) + 1 + b / (a + c))
          _ = (2 / 9) + (2 / 9) * (c / (a + b)) + (2 / 9)
            + (2 / 9) * (a / (b + c)) + (2 / 9) + (2 / 9) * (b / (a + c))   := by ring_nf
          _ = (2 / 3) + (2 / 9) * (c / (a + b)) + (2 / 9) * (a / (b + c))
                                                + (2 / 9) * (b / (a + c))   := by ring_nf
          _ = (2 / 3) + (2 / 9) * ((c / (a + b)) + (a / (b + c))
                                                 + (b / (a + c)))           := by ring_nf
          _ = (2 / 3) + (2 / 9) * (a / (b + c) + b / (a + c) + c / (a + b)) := by ring_nf

      rw [fin, add_comm] at main_le
      replace main_le := sub_le_sub main_le (le_refl (2 / 3))
      rw [add_sub_cancel_right] at main_le
      replace main_le := mul_le_mul (le_refl (9 / 2)) main_le (by positivity) (by positivity)

      -- Then we know the lower bound is 3 / 2
      convert main_le using 1
      · ring_nf
      · ring_nf
    -- The upper bound is easier
    · have one_div_rest_lt_one : ∀ {x y z : ℝ}, 0 < x → 0 < y → 0 < z → x < y + z → x / (y + z) < 1
      · intro x y z hx hy hz hxyz
        have wow := div_lt_div₀ hxyz (le_refl (y + z)) (by positivity) (by positivity)
        have ne_zero : (y + z) ≠ 0 := by positivity
        simpa only [ne_eq, not_false_eq_true, div_self ne_zero] using wow

      -- We have that `a / (b + c)`, `b / (a + c)` and `c / (a + b)` are all less than `1`.
      have a_div_le_one := one_div_rest_lt_one ha hb hc h''
      have b_div_le_one := one_div_rest_lt_one hb ha hc h'
      have c_div_le_one := one_div_rest_lt_one hc ha hb h

      -- Then the upper bound is clearly 3
      calc a / (b + c) + b / (a + c) + c / (a + b)
        _ < 1 + 1 + 1 := by gcongr
        _ = 3 := by linarith
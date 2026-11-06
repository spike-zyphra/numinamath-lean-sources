import Mathlib

/- ## - Problem 4

Let $a, b, c$ be three positive real numbers. Prove that


$$

\frac{a+b+3 c}{3 a+3 b+2 c}+\frac{a+3 b+c}{3 a+2 b+3 c}+\frac{3 a+b+c}{2 a+3 b+3 c} \geq \frac{15}{8}

$$
 -/
theorem inequalities_179418 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b + 3 * c) / (3 * a + 3 * b + 2 * c) +
    (a + 3 * b + c) / (3 * a + 2 * b + 3 * c) +
    (3 * a + b + c) / (2 * a + 3 * b + 3 * c) ≥ 15 / 8
  := by
    -- flip ≥
    apply ge_iff_le.mpr
    -- let x_0 = a, x_1 = b, x_2 = c
    let x := ![a, b, c]
    have x_eq_0 : x 0 = a := rfl
    have x_eq_1 : x 1 = b := rfl
    have x_eq_2 : x 2 = c := rfl

    -- let s = \sum_{k=i}^2 x_i
    let s := ∑ i : Fin 3, x i

    -- so s = a + b + c
    have s_eq : s = a + b + c := by
      unfold s x
      rw [Fin.sum_univ_three]
      exact rfl
    -- let S be the RHS expressed using s and x
    let S :=
        (s + 2 * (x 0)) / (3 * s - (x 0))
      + (s + 2 * (x 1)) / (3 * s - (x 1))
      + (s + 2 * (x 2)) / (3 * s - (x 2))
    convert_to 15 / 8 ≤ S
    · unfold S x
      rw [s_eq]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_zero]
      ring

    -- Express S + 6 as a sum of three terms
    have S_add_six : S + 6 = ∑ i : Fin 3, (7 * s) / (3 * s - (x i)) := by
      calc
        _ = ∑ i : Fin 3, ((s + 2 * (x i)) / (3 * s - (x i)) + 2) := by
          rw [Fin.sum_univ_three]
          ring
      _ = _ := by
          congr
          ext k
          rw [div_add']
          · ring
          · rw [s_eq]
            fin_cases k
            all_goals
            · simp only [Fin.reduceFinMk, ne_eq]
              linarith

    -- extract 7 * s from sum
    have S_add_six' : S + 6 = (7 * s) * ∑ k : Fin 3, 1 / (3 * s - (x k)) := by
      rw [S_add_six]
      nth_rw 3 [Finset.mul_sum]
      congr
      ext i
      ring

    -- We can express 8 * s as a three term sum of s and x
    have eight_s : 8*s = ∑ i : Fin 3, (3 * s - (x i)) := by
      rw [Fin.sum_univ_three, x_eq_0, x_eq_1, x_eq_2, s_eq]
      ring

    -- so we have a new expression for s
    have s_eq' : s = (1 / 8) * ∑ i : Fin 3, (3 * s - (x i)) := by
      rw [←eight_s]
      ring

    -- Then (63 / 8) is a lower bound of S + 6
    have le_S_add_six : (63 / 8) ≤ S + 6 := by

      -- rewrite S + 6 and s as similar sums
      rw [S_add_six']
      nth_rw 1 [s_eq']
      rw [←mul_assoc, mul_div, mul_one, mul_assoc]

      -- Then we just have to show 9 ≤ (∑_{k=0}^2 (s * 3 - x_k)) * ∑_{k=0}^2  1 / (s * 3 - x_k)
      have pos : (0 : ℝ) < 8 / 7 := by positivity
      apply le_of_mul_le_mul_left _ pos
      ring_nf

      -- We'll use AM-HM inequality on three numbers

      -- Convert RHS into appropriate form
      rw [Fin.sum_univ_three, Fin.sum_univ_three]
      set p := s * 3 - x 0
      set q := s * 3 - x 1
      set r := s * 3 - x 2

      have pos : (0 : ℝ) < 1 / 3 := by positivity
      apply le_of_mul_le_mul_left _ pos
      convert_to 3 ≤ ( (p + q + r) / p + (p + q + r) / q + (p + q + r) / r ) / 3
      · ring
      · ring

      -- Our three numbers
      let z := ![(p + q + r) / p, (p + q + r) / q, (p + q + r) / r]

      -- Every number is positive
      have z_pos : ∀ i ∈ Finset.univ, 0 < z i := by
        intro i ih
        fin_cases i
        all_goals
        · simp only [Fin.reduceFinMk]
          unfold z
          simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons]
          unfold p q r
          rw [x_eq_0, x_eq_1, x_eq_2, s_eq]
          ring_nf
          positivity

      -- And therefore non-negative
      have z_nonneg : ∀ i ∈ Finset.univ, 0 ≤ z i := (le_of_lt <| z_pos · ·)

      -- Every number has a weight of 1, so the sum of their weight is positive
      have pos_ones : 0 < ∑ i : Fin 3, (fun x => (1 : ℝ)) i := by positivity

      -- and 0 < 1
      have ones_pos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < (fun _ => (1 : ℝ)) i
        := fun _ _ => by positivity

      -- and 0 ≤ 1
      have ones_nonpos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ (fun _ => (1 : ℝ)) i
        := (le_of_lt <| ones_pos · ·)

      -- GM-AM
      have gm_am := @Real.geom_mean_le_arith_mean (Fin 3) Finset.univ (fun _ => 1) z ones_nonpos pos_ones z_nonneg

      -- HM-GM
      have hm_gm := @Real.harm_mean_le_geom_mean (Fin 3) Finset.univ Finset.univ_nonempty (fun _ => 1) z ones_pos pos_ones z_pos

      -- combine to get HM AM
      convert le_trans hm_gm gm_am
      -- HM is equal to LHS
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
          mul_one, one_div]
        rw [Fin.sum_univ_three]
        unfold z
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero, inv_div,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        rw [div_add_div_same, div_add_div_same]
        convert_to (3 : ℝ) = 3 / 1
        congr
        apply div_self
        · suffices yep : 0 < p + q + r
          · exact Ne.symm (ne_of_lt yep)
          unfold p q r
          rw [s_eq, x_eq_0, x_eq_1, x_eq_2]
          ring_nf
          positivity
        exact (div_one 3).symm
      -- AM is equal to RHS
      · rw [Fin.sum_univ_three, one_mul, one_mul, one_mul]
        exact rfl
      -- weights make sense: 1 + 1 + 1 = 3
      rw [Fin.sum_univ_three]
      ring

    -- Bound on S + 6 gives us our bound on S
    convert sub_le_sub_right le_S_add_six 6 using 1
    · ring
    · ring
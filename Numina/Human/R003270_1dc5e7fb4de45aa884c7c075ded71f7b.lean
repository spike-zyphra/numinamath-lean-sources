import Mathlib

/- 10. (2005 National Training Team Test) Let $a, b, c \geqslant 0, ab + bc + ca = \frac{1}{3}$, prove: $\frac{1}{a^{2} - bc + 1} + \frac{1}{b^{2} - ca + 1} + \frac{1}{c^{2} - ab + 1} \leqslant 3$. -/
theorem inequalities_165649 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 1 / 3) :
    3 ≥ 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) +
        1 / (c ^ 2 - a * b + 1) := by
    -- use ≤
    rw [ge_iff_le]

    -- 1 - 1 / 3 is positive
    have pos : (0 : ℝ) < -(1 / 3) + 1 := by norm_num

    -- the denominators are positive
    have ⟨a_bound, b_bound, c_bound⟩
      : 0 < a ^ 2 - b * c + 1
      ∧ 0 < b ^ 2 - c * a + 1
      ∧ 0 < c ^ 2 - a * b + 1
      := by
        split_ands
        all_goals
        · refine lt_of_lt_of_le pos ?_
          rw [←h, ←sub_nonneg]
          ring_nf
          positivity

    -- a + b + c is positive
    have abc_bound : 0 < a + b + c := by
      -- clearly non-negative
      have nonneg : 0 ≤ a + b + c := by positivity
      rcases lt_or_eq_of_le nonneg with h1 | h2
      · exact h1
      -- but if it's equal to zero, then all variables are zero
      · have a_eq : a = 0 := by linarith
        have b_eq : b = 0 := by linarith
        have c_eq : c = 0 := by linarith

        -- but then 0 = 1 / 3, contradiction
        rw [a_eq, b_eq, c_eq] at h
        norm_num at h

    -- let M = a / (a ^ 2 - b * c + 1) + b / (b ^ 2 - c * a + 1) + c / (c ^ 2 - a * b + 1)
    let M := a / (a ^ 2 - b * c + 1)
      + b / (b ^ 2 - c * a + 1)
      + c / (c ^ 2 - a * b + 1)

    -- let N = 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1)
    set N := 1 / (a ^ 2 - b * c + 1)
      + 1 / (b ^ 2 - c * a + 1)
      + 1 / (c ^ 2 - a * b + 1)

    -- we have that 1 ≤ M * (a + b + c)
    have M_bound : 1 ≤ M * (a + b + c) := by

      -- we apply the Cauchy-Schwarz inequality to
      -- a / (a ^ 2 - b * c + 1), b / (b ^ 2 - c * a + 1), c / (c ^ 2 - a * b + 1)
      let f := ![a / (a ^ 2 - b * c + 1), b / (b ^ 2 - c * a + 1), c / (c ^ 2 - a * b + 1)]

      -- (which is equal to M)
      have M_eq : ∑ i : Fin 3, f i = M := by
        rw [Fin.sum_univ_three]
        unfold f M
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

      -- and a * (a ^ 2 - b * c + 1), b * (b ^ 2 - c * a + 1), c * (c ^ 2 - a * b + 1)
      let g := ![a * (a ^ 2 - b * c + 1), b * (b ^ 2 - c * a + 1), c * (c ^ 2 - a * b + 1)]

      -- all terms are non-negative
      have f_nonneg : ∀ i, 0 ≤ f i := by
        intro i
        unfold f
        fin_cases i
        all_goals
        · simp
          positivity
      have g_nonneg : ∀ i, 0 ≤ g i := by
        intro i
        unfold g
        fin_cases i
        all_goals
        · simp
          positivity
      have cauchy := Real.sum_sqrt_mul_sqrt_le Finset.univ f_nonneg g_nonneg

      -- then M is part of the inequality
      rw [M_eq] at cauchy

      -- LHS is equal to a + b + c
      have mul_eq : ∑ i : Fin 3, √(f i) * √(g i) = a + b + c := by
        rw [Fin.sum_univ_three, ←Real.sqrt_mul (f_nonneg 0), ←Real.sqrt_mul (f_nonneg 1),
          ←Real.sqrt_mul (f_nonneg 2), ←Real.sqrt_sq ha, ←Real.sqrt_sq hb, ←Real.sqrt_sq hc,
          pow_two, pow_two, pow_two]
        unfold f g
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
        congr 2
        · congr 1
          field_simp
          ring_nf
        · congr 1
          field_simp
          ring_nf
        · field_simp
          ring_nf

      -- M is non-negative
      have M_nonneg : 0 ≤ M := by positivity

      -- LHS is positive
      have sum_mul_pos : 0 < ∑ i : Fin 3, √(f i) * √(g i)
        := lt_of_lt_of_eq abc_bound mul_eq.symm

      -- simplify LHS
      rw [←Real.sqrt_mul M_nonneg, Real.le_sqrt' sum_mul_pos, mul_eq] at cauchy

      -- simplify ∑ g
      have sum_g : ∑ i : Fin 3, g i = a * (a ^ 2 - b * c + 1) + b * (b ^ 2 - c * a + 1) + c * (c ^ 2 - a * b + 1) := by
        rw [Fin.sum_univ_three]
        unfold g
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

      -- then it's positive
      have g_pos : 0 < a * (a ^ 2 - b * c + 1) + b * (b ^ 2 - c * a + 1) + c * (c ^ 2 - a * b + 1) := by
        by_cases z : a = 0 ∧ b = 0 ∧ c = 0
        · rw [z.1, z.2.1, z.2.2] at abc_bound
          norm_num at abc_bound
        · rw [not_and_or, not_and_or] at z
          rcases z with h1 | h2 | h3
          · have a_pos : 0 < a := by positivity
            positivity
          · have b_pos : 0 < b := by positivity
            positivity
          · have c_pos : 0 < c := by positivity
            positivity


      -- isolate M on RHS
      rw [sum_g, ←(div_le_iff₀ g_pos)] at cauchy

      -- simplify division on LHS to get 1 / (a + b + c) ≤ M
      have factored : (a + b + c) ^ 2 / (a * (a ^ 2 - b * c + 1) + b * (b ^ 2 - c * a + 1) + c * (c ^ 2 - a * b + 1))
        = ((a + b + c) * (a + b + c)) / ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a + 1)) := by
        ring

      have canceled : ((a + b + c) * (a + b + c)) / ((a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a + 1))
        = (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a + 1) := by
        apply mul_div_mul_left
        positivity

      have one_eq : 1 = 3 * (a * b + b * c + c * a) := by
        rw [h]
        norm_num

      have reworked : (a + b + c) / (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a + 1)
        = (a + b + c) / ((a + b + c) * (a + b + c)) := by
          rw [one_eq]
          ring

      have final_cancel : (a + b + c) / ((a + b + c) * (a + b + c)) = 1 / (a + b + c) := by
        simp only [div_self_mul_self', one_div]

      rw [factored, canceled, reworked, final_cancel] at cauchy

      -- so 1 ≤ M * (a + b + c)
      exact (mul_inv_le_iff₀ abc_bound).mp cauchy

    -- recall the definition of N
    have N_eq : N = 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) := by rfl

    -- multiply both sides by (1 / 3)
    apply_fun (· * (1 / 3)) at N_eq

    -- use (1 / 3 = a * b + b * c + c * a) on RHS
    nth_rw 2 [←h] at N_eq

    -- multiplication distributes over addition
    have rhs_eq : (1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1)) * (a * b + b * c + c * a)
      = ((a * b + b * c + c * a) / (a ^ 2 - b * c + 1) + (b * c + c * a + a * b) / (b ^ 2 - c * a + 1) + (c * a + a * b + b * c) / (c ^ 2 - a * b + 1))
      := by ring

    -- rewrite RHS terms to make it similar to M and N terms
    have term_eq : ∀ {x y z : ℝ}, 0 < x ^ 2 - y * z + 1 → (x * y + y * z + z * x) / (x ^ 2 - y * z + 1)
      = x / (x ^ 2 - y * z + 1) * (x + y + z) + 1 / (x ^ 2 - y * z + 1) - 1
      := by
        intro x y z hh
        have ne_zero : (x ^ 2 - y * z + 1) ≠ 0 := by positivity
        have one_eq : 1 = (x ^ 2 - y * z + 1) / (x ^ 2 - y * z + 1) := by field_simp
        nth_rw 5 [one_eq]
        ring

    -- then we have that N / 3 = M * (a + b + c) + N - 3
    have N_div_eq : N / 3 = M * (a + b + c) + N - 3 := by
      rw [div_eq_mul_one_div N 3, N_eq, rhs_eq, term_eq a_bound, term_eq b_bound, term_eq c_bound]
      ring

    replace N_eq : (2 / 3) * N = 3 - M * (a + b + c) := by
      linarith only [N_div_eq]

    have rhs_le : 3 - M * (a + b + c) ≤ 3 - 1 := tsub_le_tsub_left M_bound 3

    rw [←N_eq] at rhs_le

    -- 3 / 2 is positive
    have pos : (0 : ℝ) < 3 / 2 := by positivity

    -- multiply both sides by 3 / 2, we get that N ≤ 3
    convert (mul_le_mul_left pos).mpr rhs_le <;> ring
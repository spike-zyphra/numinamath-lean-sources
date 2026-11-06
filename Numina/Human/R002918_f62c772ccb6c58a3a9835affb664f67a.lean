import Mathlib

open Real

/- If we have a sequence of (at least 2) positive values x which sum to 1, then every value is less than 1. -/
lemma Fun_lt_of_sum_pos_eq (x : Fin (n + 2) → ℝ)
  (pos : ∀ (i : Fin (n + 2)), 0 < x i) (sum_eq : ∑ i : Fin (n + 2), x i = 1)
  : ∀ i, x i < 1 := by
    -- assume there's some value which is at least 1
    by_contra lt_one
    simp only [not_forall, not_lt] at lt_one
    obtain ⟨i, hi⟩ := lt_one
    rw [Fin.sum_univ_succAbove x i] at sum_eq

    -- then the rest are non-positive
    have sum_nonpos : ∑ i_1 : Fin (n + 1), x (i.succAbove i_1) ≤ 0 := by linarith

    -- but the rest are positive
    have sum_pos : 0 < ∑ i_1 : Fin (n + 1), x (i.succAbove i_1) := by
      refine Finset.sum_pos ?_ Finset.univ_nonempty
      intro aa bb
      exact pos (i.succAbove aa)

    -- contradiction
    linarith

/- 4th Chinese 1989 Problem A2 x 1 , x 2 , ... , x n are positive reals with sum 1. Show that ∑ 1 n x i /√(1 - x i ) ≥ ( ∑ 1 n √x i )/√(n - 1). -/
theorem inequalities_130214 {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (hxs : ∑ i, x i = 1) :
    (∑ i, sqrt (x i)) / sqrt (n - 1) ≤ ∑ i, x i / sqrt (1 - x i) := by

    -- wlog, the x are sorted
    wlog x_mono : Monotone x
    -- if not, we sort the x values
    · have sum_eq_one : ∑ i : Fin n, (x ∘ (Tuple.sort x)) i = 1 := by
        simp only [Function.comp_apply]
        rw [Equiv.sum_comp]
        exact hxs
      -- it still has all the required properties
      have app := this (x ∘ (Tuple.sort x)) (hx <| (Tuple.sort x) ·) sum_eq_one (Tuple.monotone_sort x)

      -- the sums are just permutations
      simp only [Function.comp_apply,
        Equiv.sum_comp (Tuple.sort x) (fun i => √(x i)),
        Equiv.sum_comp (Tuple.sort x) (fun i => x i / √(1 - x i))] at app
      exact app

    -- we have 0, 1, or at least 2 values
    have n_cases : n = 0 ∨ n = 1 ∨ 2 ≤ n := by omega

    rcases n_cases with eq_zero | eq_one | pos
    -- n = 0 is trivially true
    · subst eq_zero
      norm_num
    -- n = 1 has only one element
    · subst eq_one
      -- which is equal to 1
      norm_num at hxs ⊢
      positivity
    -- when n is at least 2, let us have n' such that n = n' + 2
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := Nat.exists_eq_add_of_le' pos

      -- every x value is less than 1
      have x_le_one : ∀ i, x i < 1 := Fun_lt_of_sum_pos_eq x hx hxs

      -- ones are non-negative
      have one_pos : ∀ (i : Fin (n' + 2)), 0 ≤ (fun x => (1 : ℝ)) i := by norm_num

      -- x values are non-negative
      have x_nonneg : ∀ (i : Fin (n' + 2)), 0 ≤ x i := (le_of_lt <| hx ·)

      -- apply Cauchy-Schwarz to x and ones
      have cauchy_0 := Real.sum_sqrt_mul_sqrt_le Finset.univ x_nonneg one_pos

      -- simplify, using that x values sum to 1
      norm_num [hxs] at cauchy_0

      -- then we have that LHS is at most √((n' + 2) / (n' + 1))
      trans √((n' + 2) / (n' + 1))
      · field_simp
        ring_nf
        have ne_zero : √(1 + n') ≠ 0 := by
          rw [Real.sqrt_ne_zero]
          · norm_cast
            omega
          · norm_cast
            omega
        field_simp
        rw [div_le_div_iff_of_pos_right]
        ring_nf at cauchy_0
        exact cauchy_0
        · simp only [Real.sqrt_pos]
          norm_cast
          omega

      -- let p be the sequence 1 / √(1 - x_i)
      let p := fun i => 1 / √(1 - x i)

      -- let q be the sequence √(1 - x_i)
      let q := fun i => √(1 - x i)

      -- q is an antitone sequence
      have q_anti : Antitone q := by
        intro i j h
        refine sqrt_le_sqrt ?_
        gcongr
        exact x_mono h

      -- p is a monotone sequence
      have p_mono : Monotone p := by
        intro i j h
        simp only [p, one_div, Function.comp_apply]
        refine inv_anti₀ ?_ ?_
        simp only [sqrt_pos, sub_pos]
        exact x_le_one j
        exact q_anti h

      -- so p and x are monovary
      have hfg : Monovary p x := p_mono.monovary x_mono

      -- so we can apply Chebyshev's Inequality to p and x
      have cheby := hfg.sum_smul_sum_le_card_smul_sum

      -- multiplying terms of p and x equal x_i / √(1 - x_i)
      have mul_eq : ∀ i, p i * x i = x i / √(1 - x i) := by
        intro i
        norm_num [p]
        ring

      -- simplify the Chebyshev's Inequality application
      norm_num [mul_eq, hxs] at cheby

      -- rearranging we have (∑ p) / (n' + 2) ≤ ∑ (x_i / √(1 - x_i))
      replace cheby : (∑ i : Fin (n' + 2), p i) / (↑n' + 2) ≤ ∑ x_1 : Fin (n' + 2), x x_1 / √(1 - x x_1)
        := by
          rw [div_le_iff₀]
          linarith
          positivity

      -- we also have that p antivaries with q
      have hfg_2 : Antivary p q := p_mono.antivary q_anti

      -- so we can apply Chebyshev's Inequality to p and q too
      have cheby_2 := hfg_2.card_smul_sum_le_sum_smul_sum

      -- multiplying terms of p and q equal 1
      have mul_eq_2 : ∀ i, p i * q i = 1 := by
        intro i
        norm_num [p, q]
        refine inv_mul_cancel₀ ?_
        have lt_one := x_le_one i
        rw [Real.sqrt_ne_zero]
        linarith
        linarith

      -- simplify
      norm_num [mul_eq_2] at cheby_2

      -- Every 1 - x_i is non-negative
      have poss : ∀ (i : Fin (n' + 2)), 0 ≤ 1 - x i := by
        intro i
        simp only [sub_nonneg]
        exact le_of_lt <| x_le_one i

      -- So we can apply Cauchy-Schwarz to 1 - x_i and ones
      have cauchy := Real.sum_sqrt_mul_sqrt_le Finset.univ poss one_pos

      -- simplify
      norm_num [hxs] at cauchy
      ring_nf at cauchy

      -- the left hand side of the Cauchy-Schwarz inequality is positive
      have left_pos : 0 < ∑ x_1 : Fin (n' + 2), √(1 - x x_1) := by
        refine Fintype.sum_pos ?_
        -- every term is positive
        have all_pos : ∀ i, 0 < √(1 - x i) := by
          intro i
          simp only [sqrt_pos, sub_pos]
          exact x_le_one i
        exact lt_of_strongLT all_pos

      -- rewrite LHS so that the denominator equals the RHS of one of the cauchy inequalities
      have sqrt_eq : √((n' + 2) / (n' + 1)) = (n' + 2) / (√(1 + n') * √(2 + n')) := by
        field_simp
        ring_nf

        -- square of sqrt is identity
        have sqrt_sq : √(2 + n') ^ 2 = 2 + n' := by
          refine sq_sqrt ?_
          positivity

        rw [sqrt_sq]
        ring

      rw [sqrt_eq]

      -- then we can chain inequalities
      trans (n' + 2) / ∑ i : Fin (n' + 2), √(1 - x i)
      · apply div_le_div₀
        · linarith
        · linarith
        · exact left_pos
        · exact cauchy

      -- further chaining of inequalities
      trans (∑ i : Fin (n' + 2), p i) / (n' + 2)
      · rw [div_le_div_iff₀]
        linarith
        exact left_pos
        positivity

      -- finally we apply Chebyshev's Inequality
      exact cheby
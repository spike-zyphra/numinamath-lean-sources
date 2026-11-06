import Mathlib

/- 21. Let $x_{i}>0(i=1,2, \cdots, n)$, prove:

$$

\frac{x_{1}}{x_{2}+x_{3}+\cdots+x_{n}}+\frac{x_{2}}{x_{3}+x_{4}+\cdots+x_{n}+x_{1}}+\cdots+\frac{x_{n}}{x_{1}+x_{2}+\cdots+x_{n-1}} \geqslant \frac{n}{n-1} .

$$
 -/
theorem inequalities_260348 {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i : Fin n, 0 < x i) :
    ∑ i : Fin n, x i / (∑ j : Fin n, x j - x i) ≥ n / (n - 1)
  := by
    -- use ≤
    rw [ge_iff_le]

    -- wlog x is monotone
    wlog hm : Monotone x
    -- if it works when x is monotone, we can sort the non-monotone x and see that all the sums are the same
    · let g := Tuple.sort x
      -- use hypothesis
      convert this (x <| g ·) (hx <| g ·) (Tuple.monotone_sort x) using 1

      -- sums with permutations applied are equal
      rw [Equiv.sum_comp]
      exact (Equiv.sum_comp g (fun k ↦ x k / (∑ j, x j - x k))).symm

    -- True when n = 0 or 1, so say 2 ≤ n
    by_cases n_two : ¬2 ≤ n
    · simp only [not_le] at n_two
      interval_cases n
      · simp only [CharP.cast_eq_zero, zero_sub, zero_div, Finset.univ_eq_empty, Finset.sum_empty,
        le_refl]
      · simp only [Nat.cast_one, sub_self, div_zero, Finset.univ_unique, Fin.default_eq_zero,
          Fin.isValue, Finset.sum_singleton, le_refl]
    simp only [not_le, not_lt] at n_two

    -- sum of all x is positive
    have sum_pos : 0 < ∑ j, x j := by
      -- x is positive
      refine Fintype.sum_pos ?_
      -- make it clear that Fin n is nonempty, because n = k + 2 for some k
      obtain ⟨k, kh⟩ := Nat.exists_eq_add_of_le' n_two
      subst kh
      exact lt_of_strongLT hx

    -- Were going to use Chebyshev's inequality using f k = (∑ j, x j) - x k and g k = x k / ((∑ j, x j) - x k)
    let f := fun k : Fin n => (∑ j, x j) - x k
    let g := fun k : Fin n => x k / ((∑ j, x j) - x k)

    -- f k = (∑ j, x j) - x k is antitone
    have f_antitone : Antitone f := by
      intro aa bb cc
      exact tsub_le_tsub_left (hm cc) (∑ j, x j)
    -- g k = x k / ((∑ j, x j) - x k) is monotone
    have g_monotone : Monotone g := by
      intro aa bb cc
      obtain ⟨k, kh⟩ := Nat.exists_eq_add_of_le' n_two
      subst kh
      -- subtracting an element from the sum is still positive
      have sum_sub_pos : ∀ q, 0 < ∑ j : Fin (k + 2), x j - x q := by
        intro q
        rw [Fin.sum_univ_succAbove x q]
        simp only [add_sub_cancel_left]
        refine Fintype.sum_pos ?_
        exact lt_of_strongLT fun i => hx (q.succAbove i)

      -- cancel fractions to get a * b ≤ c * d
      refine (div_le_div_iff₀ (sum_sub_pos aa) (sum_sub_pos bb)).mpr ?_

      -- simplify both sides
      rw [mul_sub, mul_sub]
      nth_rw 2 [mul_comm]

      -- cancel common terms
      simp only [tsub_le_iff_right, sub_add_cancel]
      rw [mul_le_mul_right sum_pos]

      -- x is monotone
      exact hm cc

    -- so f antivaries with g
    have hfg : AntivaryOn f g (Finset.univ : Finset (Fin n))
      := (f_antitone.antitoneOn _).antivaryOn (g_monotone.monotoneOn _)

    -- so we can apply the Chebyshev's inequality
    have cheby := AntivaryOn.card_mul_sum_le_sum_mul_sum hfg

    -- simplify the Chebyshev's inequality
    simp only [Finset.card_univ, Fintype.card_fin] at cheby
    convert_to ↑n * (∑ j, x j) ≤ (∑ i : Fin n, f i) * ∑ i : Fin n, g i at cheby
    · congr
      unfold f g
      ext i
      refine mul_div_cancel₀ (x i) ?_
      obtain ⟨k, kh⟩ := Nat.exists_eq_add_of_le' n_two
      subst kh
      rw [Fin.sum_univ_succAbove x i]
      simp only [add_sub_cancel_left, ne_eq]
      suffices hs : 0 < ∑ i_1 : Fin (k + 1), x (i.succAbove i_1)
      · linarith only [hs]
      refine Fintype.sum_pos ?_
      exact lt_of_strongLT fun i_1 => hx (i.succAbove i_1)


    rw [Finset.sum_sub_distrib] at cheby
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at cheby
    rw [←sub_one_mul ↑n (∑ j : Fin n, x j)] at cheby

    -- RHS factor is positive
    have mul_ne_zero : 0 < (↑n - 1) * (∑ j, x j) := by
      have pos_n_pred : (0 : ℝ) < (↑n - 1) := by
        obtain ⟨k, kh⟩ := Nat.exists_eq_add_of_le' n_two
        subst kh
        simp only [Nat.cast_add, Nat.cast_ofNat, sub_pos]
        linarith only
      positivity

    -- dividing by positive constant is monotone
    have div_mono : Monotone fun k => k / ((↑n - 1) * ∑ j : Fin n, x j)
      := monotone_id.div_const <| le_of_lt mul_ne_zero

    -- we divide both sides of Chebyshev's inequality
    apply_fun fun k => k / ((↑n - 1) * (∑ j, x j)) at cheby using div_mono

    -- then the inequality is equal to our goal
    convert cheby using 1
    -- LHS division cancels
    · refine (mul_div_mul_right _ _ ?_).symm
      linarith only [sum_pos]
    -- RHS division cancels
    · refine Eq.symm (mul_div_cancel_left₀ (∑ i : Fin n, g i) ?_)
      exact (ne_of_lt mul_ne_zero).symm
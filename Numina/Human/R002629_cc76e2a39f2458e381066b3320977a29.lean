import Mathlib

/- How many three-digit numbers satisfy the property that the middle digit is the [average](https://artofproblemsolving.com/wiki/index.php/Mean) of the first and the last digits?
$(\mathrm {A}) \ 41 \qquad (\mathrm {B}) \ 42 \qquad (\mathrm {C})\ 43 \qquad (\mathrm {D}) \ 44 \qquad (\mathrm {E})\ 45$ -/
theorem number_theory_97077_third :
  Set.ncard {n : ℕ | (Nat.digits 10 n).length = 3 ∧ 2 * (Nat.digits 10 n)[1]! = ((Nat.digits 10 n)[0]! + (Nat.digits 10 n)[2]!)}
  = 45 := by {
    -- Let the three digits be ABC = n
    calc Set.ncard {n : ℕ | (Nat.digits 10 n).length = 3 ∧ 2 * (Nat.digits 10 n)[1]! = ((Nat.digits 10 n)[0]! + (Nat.digits 10 n)[2]!)}
      = Set.ncard ((fun ⟨A, B, C⟩ => Nat.ofDigits 10 [C, B, A]) '' ({⟨A, B, C⟩ : ℕ × ℕ × ℕ | 1 ≤ A ∧ A < 10 ∧ B < 10 ∧ C < 10} ∩ ({⟨A, B, C⟩ | 2 * B = C + A }))) := by {
        congr 1
        ext n
        simp only [Nat.reduceLeDiff,
          Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Prod.exists]
        refine ⟨?_, ?_⟩
        · intro ⟨aa, bb⟩
          obtain ⟨c, b, a, hl⟩ := List.length_eq_three.mp aa
          refine ⟨a, b, c, ?_⟩
          rw [←hl, Nat.ofDigits_digits]
          simp only [and_true]
          rw [hl] at bb
          simp at bb
          have non_empty : Nat.digits 10 n ≠ [] := List.ne_nil_of_length_eq_add_one aa
          have a_last : (Nat.digits 10 n).getLast non_empty = a := by {
            simp only [Nat.reduceLeDiff, hl, ne_eq, reduceCtorEq, not_false_eq_true,
              List.getLast_cons, List.cons_ne_self, List.getLast_singleton]
          }
          have a_mem : a ∈ Nat.digits 10 n := by { rw [hl]; tauto }
          have b_mem : b ∈ Nat.digits 10 n := by { rw [hl]; tauto }
          have c_mem : c ∈ Nat.digits 10 n := by { rw [hl]; tauto }
          refine ⟨⟨?_, ?_, ?_, ?_⟩, bb⟩
          · suffices : a ≠ 0
            · exact Nat.one_le_iff_ne_zero.mpr this
            rw [←a_last]
            apply Nat.getLast_digit_ne_zero
            exact Nat.digits_ne_nil_iff_ne_zero.mp non_empty
          exact Nat.digits_lt_base (by omega) a_mem
          exact Nat.digits_lt_base (by omega) b_mem
          exact Nat.digits_lt_base (by omega) c_mem
        · simp only [Nat.reduceLeDiff, forall_exists_index, and_imp]
          intro aa bb cc dd ee ff gg hh ii
          rw [←ii]
          rw [Nat.digits_ofDigits]
          simp only [List.length_cons, List.length_singleton, Nat.reduceAdd,
            List.getElem!_eq_getElem?_getD, Nat.one_lt_ofNat, List.getElem?_eq_getElem,
            List.getElem_cons_succ, List.getElem_cons_zero, Nat.default_eq_zero, Option.getD_some,
            Nat.ofNat_pos, Nat.lt_add_one, true_and]
          simp only [List.length_nil, zero_add, Nat.reduceAdd, List.length_cons,
            List.length_singleton, Nat.one_lt_ofNat, List.getElem?_eq_getElem,
            List.getElem_cons_succ, List.getElem_cons_zero, Option.getD_some, Nat.ofNat_pos,
            Nat.lt_add_one, true_and]

          exact hh
          omega
          simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq]
          simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true]
          exact ⟨gg, ff, ee⟩
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons, List.cons_ne_self,
            List.getLast_singleton, forall_const]
          exact Nat.not_eq_zero_of_lt dd
      }

    -- Converting digits to a number is injective
    _ = Set.ncard (({⟨A, B, C⟩ : ℕ × ℕ × ℕ | 1 ≤ A ∧ A < 10 ∧ B < 10 ∧ C < 10} ∩ ({⟨A, B, C⟩ | 2 * B = C + A }))) := by {
        refine Set.ncard_image_of_injOn ?_
        intro ⟨a1, b1, c1⟩ ⟨⟨al1, au1, bu1, cu1⟩, f1⟩ ⟨a2, b2, c2⟩ ⟨⟨al2, au2, bu2, cu2⟩, f2⟩ eq
        simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero] at eq
        simp only [Prod.mk.injEq]
        omega
      }

    -- C has to have the same parity as A, which limits its possible values
    _ = Set.ncard ({⟨A, B, C⟩ : ℕ × ℕ × ℕ | 1 ≤ A ∧ A < 10 ∧ B < 10 ∧ if Even A then C ∈ [0, 2, 4, 6, 8] else C ∈ [1, 3, 5, 7, 9]} ∩ ({⟨A, B, C⟩ | 2 * B = C + A })) := by {
      congr 1
      ext ⟨a, b, c⟩
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_cons, List.mem_singleton,
        and_congr_left_iff, and_congr_right_iff, List.not_mem_nil, or_false]
      intro eq aa ah bh
      have even_eq : Even c ↔ Even a := by {
        have ev_2 : Even (2*b) := even_two_mul b
        rw [eq] at ev_2
        exact Nat.even_add.mp ev_2
      }
      refine ⟨?_, ?_⟩
      intro ch
      split_ifs with h
      have c_ev : Even c := even_eq.mpr h
      rw [Nat.even_iff] at c_ev
      omega
      have c_ev : ¬Even c := (iff_false_right h).mp even_eq
      rw [Nat.even_iff] at c_ev
      omega

      split_ifs with h <;> omega
    }

    -- B is determined by A and C, i.e. B = (A + C) / 2
    _ = Set.ncard ((fun ⟨A, C⟩ => (⟨A, (A + C) / 2, C⟩ : ℕ × ℕ × ℕ)) '' {⟨A, C⟩ : ℕ × ℕ | 1 ≤ A ∧ A < 10 ∧ if Even A then C ∈ [0, 2, 4, 6, 8] else C ∈ [1, 3, 5, 7, 9]}) := by {
      congr 1
      ext ⟨a, b, c⟩
      simp only [List.mem_cons, List.mem_singleton, Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_image, Prod.mk.injEq, Prod.exists]
      simp only [List.not_mem_nil, or_false]
      refine ⟨?_, ?_⟩
      intro ⟨⟨bb, cc, ⟨dd, ee⟩⟩, gg⟩
      refine ⟨a, c, ?_⟩
      simp only [ee, and_true, true_and]
      refine ⟨⟨bb, cc⟩, ?_⟩
      omega
      simp only [forall_exists_index, and_imp]
      intro aa cc dd ee ff gg hh ii
      subst gg
      subst ii
      split_ifs at * with h <;> {rw [Nat.even_iff] at h; omega }
    }
    -- Consider just A and C
    _ = Set.ncard ({⟨A, C⟩ : ℕ × ℕ | 1 ≤ A ∧ A < 10 ∧ if Even A then C ∈ [0, 2, 4, 6, 8] else C ∈ [1, 3, 5, 7, 9]}) := by {
        refine Set.ncard_image_of_injective _ ?_
        intro ⟨a1, a2⟩ ⟨b1, b2⟩ cc
        rw [Prod.mk.injEq, Prod.mk.injEq] at cc
        rw [Prod.mk.injEq]
        exact ⟨cc.1, cc.2.2⟩
    }
    -- Then we know that there's 9 values of A and 5 values of C
    _ = Set.ncard ((fun (⟨A', C'⟩ : ℕ × ℕ) => (⟨A', if Even A' then C' * 2 else C' * 2 + 1⟩ : ℕ × ℕ)) '' ((Finset.Icc 1 9) ×ˢ (Finset.Icc 0 4))) := by {
      congr 1
      ext ⟨A, C⟩
      simp only [List.mem_cons, List.mem_singleton, Set.mem_setOf_eq, Finset.coe_Icc,
        Set.Icc_prod_Icc, Prod.mk_one_one, Set.mem_image, Set.mem_Icc, Prod.mk.injEq, Prod.exists,
        Prod.mk_le_mk]
      refine ⟨?_, ?_⟩
      intro ⟨aa1, aa2, aa3⟩
      simp only [List.not_mem_nil, or_false] at aa3
      refine ⟨A, ?_⟩
      split_ifs at * with h
      refine ⟨C / 2, ?_⟩
      omega
      refine ⟨(C-1) / 2, ?_⟩
      omega
      intro hh
      obtain ⟨A', B', ⟨⟨la, lb⟩, ⟨ua, ub⟩⟩, hAB2, hAB3⟩ := hh
      subst hAB2
      simp only [List.not_mem_nil, or_false]
      refine ⟨la, ?_, ?_⟩
      exact Nat.lt_add_one_of_le ua
      split_ifs at * with h
      interval_cases B' <;> tauto
      interval_cases B' <;> tauto
    }
    _ = Set.ncard ((Finset.Icc 1 9) ×ˢ (Finset.Icc 0 4)) := by {
        refine Set.ncard_image_of_injective _ ?_
        intro ⟨a1, a2⟩ ⟨b1, b2⟩ cc
        simp only [Prod.mk.injEq] at cc
        obtain ⟨c1, c2⟩ := cc
        subst c1
        split_ifs at c2 with h
        simp only [mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at c2
        exact congrArg (Prod.mk a1) c2
        simp only [add_left_inj, mul_eq_mul_right_iff, OfNat.ofNat_ne_zero, or_false] at c2
        exact congrArg (Prod.mk a1) c2
    }
    _ = ((Finset.Icc 1 9).product (Finset.Icc 0 4)).card := by {
      rw [← (Set.ncard_coe_Finset _)]
      congr 1
      exact Set.toFinset_inj.mp rfl
    }
    -- So the total is 45
    _ = 9 * 5 := by decide
    _ = 45 := by decide
}
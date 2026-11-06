import Mathlib

open Finset

/-1. Existe-t-il des nombres $a_{0}, \ldots, a_{2020}$ valant -1 ou 1 tels que $a_{0} \times a_{1}+a_{1} \times a_{2}+\cdots+a_{2019} \times$ $a_{2020}+a_{2020} \times a_{0}=1010 ?$
2. Existe-t-il des nombres $a_{1}, \ldots, a_{2020}$ valant -1 ou 1 tels que $a_{1} \times a_{2}+a_{2} \times a_{3}+\cdots+a_{2019} \times$ $a_{2020}+a_{2020} \times a_{1}=1010 ?$-/
theorem number_theory_607322 : ¬ ∃ (a : ℕ → ℤ), Set.MapsTo a (range 2021) {-1, 1} ∧
    (∑ i ∈ range 2020, a i * a (i + 1) + a 2020 * a 0 = 1010) ∨ Set.MapsTo a (Icc 1 2020) {-1, 1} ∧
    ∑ i ∈ Icc 1 2019, a i * a (i + 1) + a 2020 * a 1 = 1010 := by
  push_neg; intro a; constructor
  -- Assume the contrary that we have the summation equal to $1010$, we can find a contradiction by modulo $2$
  · intro ha h; simp [Set.MapsTo] at ha
    set n := 2020 with hn; clear_value n
    apply_fun fun t => t % 2 at h
    rw [Int.add_emod, sum_int_mod] at h
    have : ∀ i ∈ range n, a i * a (i + 1) % 2 = 1 := by
      simp; intro i ilt; have ai := @ha i (by omega)
      have ai1 := @ha (i+1) (by omega)
      rcases ai with ai|ai; all_goals
      rw [ai]; omega
    rw [sum_congr rfl this] at h
    have a0 := @ha 0 (by omega)
    have an := @ha n (by omega)
    rcases a0 with a0|a0; all_goals
    norm_num [a0] at h; omega
-- Assume the contrary that we have the summation equal to $1010$, we first partition $[1, 2019]$ according to the signs of $a_i*a_(i+1)$
  intro ha h; simp [Set.MapsTo] at ha
  set n := 2019 with hn; clear_value n
  let P := filter (fun i => a i * a (i + 1) = 1) (Icc 1 n)
  let N := filter (fun i => a i * a (i + 1) = -1) (Icc 1 n)
  have hP : ∀ i ∈ P, a i * a (i + 1) = 1 := by
    intro i imem; simp [P] at imem
    exact imem.right
  have hN : ∀ i ∈ N, a i * a (i + 1) = -1 := by
    intro i imem; simp [N] at imem
    exact imem.right
  have disj : Disjoint P N := by
    rw [disjoint_filter]
    intros; omega
  have PuN : P ∪ N = Icc 1 n := by
    rw [← filter_union_filter_neg_eq (fun i => a i * a (i + 1) = 1) (Icc 1 n)]
    congr 1; apply filter_congr; simp
    intro i ige ile; have ai := @ha i (by omega) (by omega)
    have ai1 := @ha (i+1) (by omega) (by omega)
    rcases ai with ai|ai; all_goals
    rw [ai]; omega
  rw [← PuN, sum_union disj] at h
  rw [sum_congr rfl hP, sum_congr rfl hN] at h
  simp [← sub_eq_add_neg] at h
  let cadd := PuN; apply_fun fun t => #t at cadd
  simp [card_union_of_disjoint disj] at cadd
-- Prove that the product of all $a_i*a_(i+1)$'s are $1$
  have h' : (∏ i ∈ Icc 1 n, a i * a (i + 1)) * (a 2020 * a 1) = 1 := by
    suffices : (∏ i ∈ Icc 1 n, a i * a (i + 1)) * (a 2020 * a 1) =
    ∏ i ∈ Icc 1 (n + 1), a i ^ 2
    · rw [this]; have : ∀ i ∈ Icc 1 (n + 1), a i ^ 2 = 1 := by
        simp; intros
        rw [or_comm]; apply ha
        all_goals omega
      simp [prod_congr rfl this]
  -- Generalize $n$ to any positive integer $l$ less than $2020$
    rw [show 2020 = n+1 by omega]
    have lpos : 0 < n := by omega
    have llt : n < 2020 := by simp [hn]
    generalize n = l at lpos llt
  -- Apply induction on $l$ to finish the goal
    induction l with
    | zero => simp at lpos
    | succ l ih =>
      by_cases h : l = 0
      · simp [h, show Icc 1 2 = {1, 2} by rfl]
        ring
      specialize ih (by omega) (by omega)
      rw [prod_Icc_succ_top, prod_Icc_succ_top, ← ih]
      ring; all_goals simp
-- Split the production in `h'` according to our partition
  rw [← PuN, prod_union disj] at h'
  simp [prod_congr rfl hP, prod_congr rfl hN] at h'
-- Finish the goal by splitting to two cases depending on the parity of $#N$
  by_cases par : #N % 2 = 0
  · rw [Even.neg_one_pow, one_mul] at h'
    have a1 := @ha 1 (by simp) (by simp)
    have a2020 := @ha 2020 (by simp) (by simp)
    rcases a1 with a1|a1
    any_goals simp [a1] at h h'; omega
    rw [Nat.even_iff]; exact par
  rw [Odd.neg_one_pow, neg_one_mul] at h'
  have a1 := @ha 1 (by simp) (by simp)
  have a2020 := @ha 2020 (by simp) (by simp)
  rcases a1 with a1|a1
  any_goals simp [a1] at h h'; omega
  rw [Nat.odd_iff]; omega
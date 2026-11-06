import Mathlib

/-4. (CZS 1) $)^{\mathrm{IMO} 4}$ For what natural numbers $n$ can the product of some of the numbers $n, n+1, n+2, n+3, n+4, n+5$ be equal to the product of the remaining ones?-/
theorem other_24864 : ∀ n : ℕ, ¬ ∃ U V : Finset ℕ, U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧
    U ∪ V = Finset.Icc n (n+5) ∧ ∏ i ∈ U, i = ∏ j ∈ V, j := by
-- Introduce the natural number $n$ and two sets $U$, $V$ satisfying the assumptions, then prove by contradiction
  intro n h; rcases h with ⟨U, V, _, _, UdisjV, UuniV, pdeq⟩
-- Prove the lemma that any square mod $7$ is not equal to $6$
  have lm : ∀ n, n^2 % 7 ≠ 6 := by
    intro n hn
    have : n % 7 < 7 := by apply Nat.mod_lt; norm_num
    have := Nat.mod_add_div n 7
    interval_cases (n % 7)
    any_goals rw [← this] at hn; ring_nf at hn
    · rw [Nat.mul_mod] at hn; simp at hn
    any_goals repeat rw [Nat.add_mod, Nat.mul_mod] at hn; simp at hn
-- Prove the following simple fact that Finset.Icc n (n+5) is the same as ${n, n+1, n+2, n+3, n+4, n+5}$
  have icc_eq : Finset.Icc n (n+5) = {n, n+1, n+2, n+3, n+4, n+5} := by
    rw [← Nat.Icc_insert_succ_left, ← Nat.Icc_insert_succ_left, ← Nat.Icc_insert_succ_left]
    rw [← Nat.Icc_insert_succ_left, ← Nat.Icc_insert_succ_left]; simp
    any_goals linarith
-- Split the goal to two cases : $7$ divides the product $n(n+1)(n+2)(n+3)(n+4)(n+5)$ or not
  by_cases dvd7 : 7 ∣ ∏ k ∈ Finset.Icc n (n+5), k
  -- In the first case, prove that there exists only one number $w$ in Finset.Icc n (n+5) such that $7$ divides $w$
  · rw [Prime.dvd_finset_prod_iff] at dvd7
    rcases dvd7 with ⟨w, ⟨hw1, hw2⟩⟩
    have aux: ∀ y ∈ Finset.Icc n (n+5), y ≠ w → ¬ 7 ∣ y := by
      intro y hy1 hy2 hy3; rw [ne_iff_lt_or_gt] at hy2
      simp at hw1 hy1; rcases hy2 with h'|h'
      · suffices : 7 ∣ w - y
        · apply Nat.le_of_dvd at this; zify at hw1 hy1 h' this
          rw [Nat.cast_sub] at this; any_goals linarith
          rw [Nat.sub_pos_iff_lt]; assumption
        apply Nat.dvd_sub; linarith; any_goals assumption
      suffices : 7 ∣ y - w
      · apply Nat.le_of_dvd at this; zify at hw1 hy1 h' this
        rw [Nat.cast_sub] at this; any_goals linarith
        rw [Nat.sub_pos_iff_lt]; assumption
      apply Nat.dvd_sub; linarith; any_goals assumption
  -- Split the goal to two cases : $w$ is in $U$ or $V$
  -- In any case, applying pdeq allows us to find another element $y$ in Finset.Icc n (n+5) such that $7$ divides $y$
  -- contradicting to the fact that there is only one element $w$ which is a multiple of $7$
    rw [← UuniV] at hw1; simp at hw1; rcases hw1 with h|h
    · have : 7 ∣ ∏ i ∈ U, i := by
        rw [Prime.dvd_finset_prod_iff]; use w; rw [← Nat.prime_iff]; norm_num
      rw [pdeq, Prime.dvd_finset_prod_iff] at this; rcases this with ⟨y, ⟨hy1, hy2⟩⟩
      suffices : y ≠ w
      · apply aux at this; contradiction
        rw [← UuniV]; simp; right; assumption
      intro h'; rw [Finset.disjoint_iff_inter_eq_empty] at UdisjV
      have : U ∩ V ≠ ∅ := by
        rw [← Finset.nonempty_iff_ne_empty]; use y; simp
        constructor; rw [h']; any_goals assumption
      contradiction
      rw [← Nat.prime_iff]; norm_num
    have : 7 ∣ ∏ i ∈ V, i := by
      rw [Prime.dvd_finset_prod_iff]; use w; rw [← Nat.prime_iff]; norm_num
    rw [← pdeq, Prime.dvd_finset_prod_iff] at this; rcases this with ⟨y, ⟨hy1, hy2⟩⟩
    suffices : y ≠ w
    · apply aux at this; contradiction
      rw [← UuniV]; simp; left; assumption
    intro h'; rw [Finset.disjoint_iff_inter_eq_empty] at UdisjV
    have : U ∩ V ≠ ∅ := by
      rw [← Finset.nonempty_iff_ne_empty]; use y; simp
      constructor; assumption; rw [h']; assumption
    contradiction
    any_goals rw [← Nat.prime_iff]; norm_num
-- For the case when $7$ does not divide the product $n(n+1)(n+2)(n+3)(n+4)(n+5)$, we first apply division with remainder on $n$ and $7$
  have : n % 7 < 7 := by apply Nat.mod_lt; norm_num
  have div7 := Nat.mod_add_div n 7
-- Prove that the remainder of $n$ divided by $7$ is $1$, we will prove by contradiction and exclude all possible remainders
  have mod7 : n % 7 = 1 := by
    by_contra h'; push_neg at h'
    interval_cases (n % 7)
    any_goals suffices : 7 ∣ ∏ k ∈ Finset.Icc n (n + 5), k; contradiction; rw [Prime.dvd_finset_prod_iff]
    any_goals rw [← Nat.prime_iff]; norm_num
    · use n; simp; simp at div7; symm at div7; use n/7
    · contradiction
    · use n+5; simp; use n/7+1; nth_rw 1 [← div7]; ring
    · use n+4; simp; use n/7+1; nth_rw 1 [← div7]; ring
    · use n+3; simp; use n/7+1; nth_rw 1 [← div7]; ring
    · use n+2; simp; use n/7+1; nth_rw 1 [← div7]; ring
    · use n+1; simp; use n/7+1; nth_rw 1 [← div7]; ring
-- Rewrite the assumption div7
  rw [mod7] at div7; symm at div7; rw [add_comm] at div7
-- Compute the remainder of the product $n(n+1)(n+2)(n+3)(n+4)(n+5)$ divided by $7$ and find out it is $6$
  have pdmod7: (∏ k ∈ Finset.Icc n (n + 5), k) % 7 = 6 := by
    rw [icc_eq]; simp; rw [Nat.mul_mod, mod7]; simp
    rw [Nat.mul_mod, div7, add_assoc, Nat.add_mod]; simp
    repeat rw [mul_comm, mul_assoc]; norm_num; rw [mul_assoc, Nat.mul_mod, add_assoc, Nat.add_mod]; simp
    rw [mul_comm, mul_assoc]; norm_num; rw [Nat.mul_mod, add_assoc, Nat.add_mod]; norm_num
-- Use pdeq to rewrite the product $n(n+1)(n+2)(n+3)(n+4)(n+5)$ as a square, we find that this contradicts to the lemma lm we proved at the very beginning
  rw [← UuniV, Finset.prod_union, pdeq, ← pow_two] at pdmod7
  have := lm (∏ j ∈ V, j); contradiction
  assumption
import Mathlib
open Mathlib
/--
Let $S$ be a list of positive integers--not necessarily distinct--in which the number $68$ appears. The average (arithmetic mean) of the numbers in $S$ is $56$. However, if $68$ is removed, the average of the remaining numbers drops to $55$. What is the largest number that can appear in $S$?
-/
lemma algebra_694 (x : ℕ) (hX : 0 < x) (hM : IsGreatest {x | ∃ s : Multiset ℕ, (∀ k ∈ s, 0 < k) ∧ x ∈ s ∧ 68 ∈ s ∧ (↑s.sum : ℚ) / s.card = 56 ∧ (↑(s.erase 68).sum : ℚ) / (s.card - 1) = 55} x) : x = 649 := by
  rcases hM with ⟨⟨s, ⟨hp, ⟨hm, ⟨hM, ⟨hB, hA⟩⟩⟩⟩⟩, hR⟩
  rw [mem_upperBounds] at hR
  simp_rw [Set.mem_setOf] at hR
  -- Prove 649 ≤ x by supplying witness consisting of eleven 1s and one 660-11=649
  have lb := hR 649 ⟨{1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 68, 649}, by native_decide⟩
  -- Now prove x ≤ 649
  -- ↑(68 + (s.erase 68).sum) / ↑(Multiset.card s) = 58
  have step := Multiset.sum_erase hM
  rw [← step, (by norm_num : (↑(68 + (s.erase 68).sum) : ℚ) = (68 : ℚ) + (↑(s.erase 68).sum : ℚ))] at hB
  have nonzero := Multiset.card_pos_iff_exists_mem.2 ⟨_, hM⟩
  have nonzero2 : Multiset.card s ≠ 0 := by exact Nat.not_eq_zero_of_lt nonzero
  have nonzero3 : (↑(Multiset.card s) : ℚ) ≠ 0 := by exact Nat.cast_ne_zero.mpr nonzero2
  -- We are given that \begin{align*} \frac{s+68}{n+1}&=56,
  have sl : (68 + (↑(s.erase 68).sum : ℚ)) = 56 * (↑(Multiset.card s) : ℚ) := ((eq_mul_inv_iff_mul_eq₀ nonzero3).mp (Eq.symm hB)).symm
  have nonzero4 : (s.erase 68).card ≠ 0 := by
    intro d
    have ak : (↑(s.erase 68).sum : ℚ) / (↑(Multiset.card s) - 1) ≠ 0 := by
      rw [hA]; norm_num
    rw [div_ne_zero_iff] at ak
    rw [Multiset.card_eq_zero] at d
    rw [d] at ak
    norm_num at ak
  have nonzero5 : (↑(Multiset.card (s.erase 68)) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr nonzero4
  have skd := Multiset.card_erase_add_one hM
  have skw : (↑(Multiset.card (s.erase 68)) : ℚ) = (↑s.card : ℚ) - 1 := by qify at *; linarith
  rw [skw] at nonzero5
  -- \\ \frac{s}{n}&=55. \end{align*}
  have sr := ((eq_mul_inv_iff_mul_eq₀ nonzero5).mp (Eq.symm hA)).symm
  -- Clearing denominators, we have \begin{align*} s+68&=56n+56, \\ s&=55n. \end{align*} Subtracting the equations, we get $68=n+56,$ from which $n=12.$
  have www : Multiset.card s = 13 := by qify at *; linarith
  -- It follows that $s=660.$
  have ddd : (s.erase 68).sum = 660 := by
    rw [www] at sr
    norm_num at sr
    qify at *
    norm_num at *
    exact sr
  have me := (Multiset.mem_erase_of_ne (by linarith : x ≠ 68)).2 hm
  have tl := Multiset.sum_erase me
  rw [ddd] at tl
  -- Sum of a multiset is at least the cardinality of the multiset
  have lbb : ∀ (s : Multiset ℕ) (hM : ∀ x, x ∈ s → 0 < x), s.card ≤ s.sum := by
    intros s hM
    induction' s using Multiset.induction with ga gb gc
    · decide
    · simp only [Multiset.card_cons, Multiset.sum_cons]
      have st1 := hM ga (by simp only [Multiset.mem_cons, true_or])
      have := gc (fun d e => hM d (Multiset.mem_cons_of_mem e))
      linarith
  -- We prove 11 ≤ ((s.erase 68).erase x).sum
  have top := lbb ((s.erase 68).erase x) (fun gn gt => by
    apply hp
    by_cases h11 : gn = x
    · rw [h11]; exact hm
    rw [Multiset.mem_erase_of_ne h11] at gt
    by_cases h11 : gn = 68
    · rw [h11]; exact hM
    rw [Multiset.mem_erase_of_ne h11] at gt
    exact gt)
  rw [Multiset.card_erase_of_mem me, Multiset.card_erase_of_mem hM, www] at top
  norm_num at top
  -- x = 649
  zify at *; linarith
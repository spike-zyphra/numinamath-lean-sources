import Mathlib

open Finset

/-13. The sum of 10 distinct positive integers is 100 . What is the largest possible value of any of the 10 integers?
A 55
В 56
С 60
D 65
E 91-/
theorem number_theory_233473 : IsGreatest {n : ℕ | ∃ a : Fin 10 → ℕ, a.Injective ∧ (∀ i, a i > 0) ∧
    (∑ i, a i) = 100 ∧ n ∈ image a Finset.univ} 55 := by
-- Rewrite the goal to an existential subgoal and an upperbound subgoal
  simp [IsGreatest, upperBounds]; constructor
  --The minimum possible sum of nine distinct positive integers is $1+2+3+4+5+6+7+8+9=45$. Hence the largest possible integer in the sum is $100-45=55$.
  · let a : Fin 10 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 55]
    use a; split_ands
    · apply StrictMono.injective
      intro i j h; fin_cases i
      all_goals simp at h; simp [a]
      all_goals fin_cases j; all_goals simp at h
      all_goals norm_num
      apply Nat.lt_add_one
      all_goals exact Nat.lt_of_sub_eq_succ rfl
    · intro i; fin_cases i
      all_goals norm_num [a]
    · rw [sum_fin_eq_sum_range]
      simp [show range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by decide, a]
      rfl
    use 9; rfl
-- To show $55$ is an upperbound, we first give an ordering to $a_i$'s using `orderEmbOfFin`
  intro l a ainj apos asum t ht
  rw [← ht]; clear ht l
  have cimg : #(image a Finset.univ) = 10 := by
    rw [card_image_of_injective _ ainj]; simp
  set s := image a Finset.univ
  have aux1 : ∀ i : Fin 10,  a i ∈ Set.range ⇑(s.orderEmbOfFin cimg) := by simp [s]
  simp only [Set.mem_range] at aux1; rcases aux1 t with ⟨t', ht'⟩
  have aux2 : ∀ j : Fin 10, (s.orderEmbOfFin cimg) j ∈ s := by simp [s]
  replace aux2 : ∀ j : Fin 10, ∃ i : Fin 10, (s.orderEmbOfFin cimg) j = a i := by
    intro j; specialize aux2 j; rw [mem_image] at aux2
    simp at aux2; rcases aux2 with ⟨i, hi⟩
    use i; rw [hi]
  choose tof h1 using aux1; choose invf h2 using aux2
-- The ordering is strictly increasing
  have emono := OrderEmbedding.strictMono (s.orderEmbOfFin cimg)
  have aux3 : Function.LeftInverse invf tof := by
    intro i; apply ainj; rw [← h2, ← h1]
  have aux4 : Function.RightInverse invf tof := by
    intro i; apply emono.injective; rw [h1, h2]
-- Define a permutation of $Fin 10$ according to this ordering and rewrite the sum of $a_i$'s
  let e := Equiv.mk tof invf aux3 aux4
  rw [Fintype.sum_equiv e a ⇑(s.orderEmbOfFin cimg)] at asum
-- For this ordering, we have $i+1≤ (s.orderEmbOfFin cimg) i$
  have aux5 : ∀ i : Fin 10, i.val + 1 ≤ (s.orderEmbOfFin cimg) i := by
    intro i; induction i using Fin.induction with
    | zero => simp [h2]; specialize apos (invf 0); omega
    | succ i ih =>
      simp at ih; simp; rw [← Nat.lt_iff_add_one_le]
      apply lt_of_le_of_lt ih; apply emono
      exact Fin.castSucc_lt_succ i
-- Apply `aux5` to $0, 1, ..., 8$, `asum` will give the desired upper bound
  have : t' ≤ 9 := by rw [Fin.le_def]; exact Fin.is_le t'
  rw [← emono.le_iff_le] at this
  rw [← ht']; apply le_trans this
  have := aux5 0; have := aux5 1; have := aux5 2; have := aux5 3
  have := aux5 4; have := aux5 5; have := aux5 6; have := aux5 7
  have := aux5 8
  simp [Fin.sum_univ_def, show (List.finRange 10) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] by rfl] at asum; omega
  intro i; simp [e]; rw [h1]

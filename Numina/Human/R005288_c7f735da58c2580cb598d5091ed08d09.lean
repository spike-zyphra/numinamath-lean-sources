import Mathlib

open Finset

/-Soient $\mathrm{m}, \mathrm{n}$ et $x$ des entiers strictement positifs. Montrer que

$$
\sum_{i=1}^{n} \min \left(\left\lfloor\frac{x}{i}\right\rfloor, m\right)=\sum_{i=1}^{m} \min \left(\left\lfloor\frac{x}{i}\right\rfloor, n\right)
$$-/
theorem number_theory_607420 (x m n : ℕ) : ∑ i ∈ Icc 1 n, min (x / i) m =
    ∑ i ∈ Icc 1 m, min (x / i) n := by
-- Denote the set of $(a, b)$ such that $a ∈ [1, m]$, $b ∈ [1, n]$ and $a * b ≤ x$ by $S$
  let S := {p ∈ Icc 1 m ×ˢ Icc 1 n | p.1 * p.2 ≤ x}
-- Prove that the projection onto first coordinates maps $S$ to $[1, m]$
  have p1 : Set.MapsTo Prod.fst S.toSet (Icc 1 m).toSet := by
    simp [Set.MapsTo, S]; omega
-- Compute the cardinality of each fiber
  have f1 : ∀ b ∈ Icc 1 m, #{a ∈ S | a.1 = b} = min (x / b) n := by
    simp; intro b bge ble
    have : image (fun j => (b, j)) (Icc 1 (min (x / b) n)) = {a ∈ S | a.1 = b} := by
      simp [Finset.ext_iff, S, and_assoc]
      intro s t; constructor
      · rintro ⟨u, uge, ule1, ule2, beqs, ueqt⟩
        simp [← beqs] at *; clear beqs s
        simp [ueqt] at *; clear ueqt u
        split_ands; any_goals assumption
        rw [Nat.le_div_iff_mul_le] at ule1
        rw [mul_comm]; exact ule1
        omega
      rintro ⟨sge, sle, tge, tle, hmul, seqb⟩
      use t; simp [seqb] at *; clear seqb s
      split_ands; any_goals assumption
      rw [Nat.le_div_iff_mul_le, mul_comm]
      exact hmul; omega
    rw [← this, card_image_of_injective]
    simp; intro i j hij
    simp at hij; exact hij
-- Prove that the cardinality of $S$ is RHS of the identity in the goal
  have c1 := card_eq_sum_card_fiberwise p1
  rw [sum_congr rfl f1] at c1; rw [← c1]
-- Prove that the projection onto second coordinates maps $S$ to $[1, m]$
  replace p1 : Set.MapsTo Prod.snd S.toSet (Icc 1 n).toSet := by
    simp [Set.MapsTo, S]; omega
-- Compute the cardinality of each fiber
  replace f1 : ∀ b ∈ Icc 1 n, #{a ∈ S | a.2 = b} = min (x / b) m := by
    simp; intro b bge ble
    have : image (fun j => (j, b)) (Icc 1 (min (x / b) m)) = {a ∈ S | a.2 = b} := by
      simp [Finset.ext_iff, S, and_assoc]
      intro s t; constructor
      · rintro ⟨u, uge, ule1, ule2, ueqs, beqt⟩
        simp [← beqt] at *; clear beqt t
        simp [ueqs] at *; clear ueqs u
        split_ands; any_goals assumption
        rw [Nat.le_div_iff_mul_le] at ule1
        exact ule1; omega
      rintro ⟨sge, sle, tge, tle, hmul, teqb⟩
      use s; simp [teqb] at *; clear teqb t
      split_ands; any_goals assumption
      rw [Nat.le_div_iff_mul_le]
      exact hmul; omega
    rw [← this, card_image_of_injective]
    simp; intro i j hij
    simp at hij; exact hij
-- Apply `card_eq_sum_card_fiberwise` again to finish the goal
  replace c1 := card_eq_sum_card_fiberwise p1
  rw [sum_congr rfl f1] at c1; omega
import Mathlib

open Pointwise Finset

/- Soit $S$ un ensemble d'entiers. On dit que $S$ est insommable si, pour tous les entiers $x$ et $y$ appartenant à $S$, la somme $x+y$ n'appartient pas à $S$. Pour tout entier $n \geqslant 1$, on note $s_{n}$ le nombre de sous-ensembles de $\{1,2, \ldots, 2 n\}$ qui sont insommables.
Démontrer que $s_{n} \geqslant 2^{n}$. -/
theorem combinatorics_605695 {s : ℕ → ℕ} : let insommable : Finset ℕ → Prop := fun S => (S + S) ∩ S = ∅;
(∀ n, s n = {T ∈ (Icc 1 (2 * n)).powerset | insommable T}.card) → ∀ n ≥ 1, s n ≥ 2 ^ n := by
-- Introduce assumptions
  intro insommable hs n hn; rw [ge_iff_le, hs]
-- Prove that the powerset of $[n+1, 2*n]$ is contained in the set of insommable subsets
  have key : (Icc (n + 1) (2 * n)).powerset ⊆ {T ∈ (Icc 1 (2 * n)).powerset | insommable T} := by
    simp [subset_iff, insommable]; intro S hS; constructor
    · intro i hi; specialize hS hi; constructor; all_goals omega
    simp [Finset.ext_iff, mem_add]; intro a x hx y hy haxy ha
    have := hS hx; have := hS hy; have := hS ha; omega
-- Prove the goal by applying card_le_card to the key lemma
  apply card_le_card at key; simp at key; nth_rw 1 [two_mul, Nat.add_sub_cancel] at key
  exact key
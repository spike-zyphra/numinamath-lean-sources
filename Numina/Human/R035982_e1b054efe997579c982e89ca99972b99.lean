import Mathlib

open Finset

theorem algebra_235071 {a : ℕ → ℤ} (ha1 : a 1 = -1)(ha : ∀ k≥1, a (k+1) = -1 - a k):
    a 1989 = -1 ∧ a 1990 = 0 := by
    
    --We use induction to show that if n is odd, then a n = - 1 and if n is even, then a n = 0.
    have lem: ∀m:ℕ, (Odd (m+1) → a (m+1) = -1) ∧ (Even (m+1) → a (m+1) = 0) := by 
      intro m
      induction' m with m hm
      simp
      exact ha1

      constructor
      intro hp
      have mp1: Even (m+1) := by 
        by_contra oddmp1
        have oddmp1 : Odd (m+1) := by
          exact Nat.not_even_iff_odd.mp oddmp1
        have evenmp1p1: Even (m+1+1) := by exact Odd.add_one oddmp1
        have : ¬ Odd (m+1+1) := by exact Nat.not_odd_iff_even.mpr evenmp1p1
        contradiction
      apply hm.right at mp1
      specialize ha (m+1)
      have : m+1 ≥ 1 := by linarith
      apply ha at this
      rw [mp1] at this;
      norm_num at this
      exact this

      intro hp
      have mp1: Odd (m+1) := by 
        by_contra evenmp1
        have evenmp1: Even (m+1) := by exact Nat.not_odd_iff_even.mp evenmp1
        have oddmp1p1: Odd (m+1+1) := by exact Even.add_one evenmp1
        have : ¬ Even (m+1+1) := by exact Nat.not_even_iff_odd.mpr oddmp1p1
        contradiction
      apply hm.left at mp1
      specialize ha (m+1)
      have : m+1 ≥ 1 := by linarith
      apply ha at this
      rw [mp1] at this
      norm_num at this
      exact this
    
    --The results simply follows from the previous lemma.
    have cla1: (Odd (1988 + 1) → a (1988 + 1) = -1) := by exact (lem 1988).left
    have cla2: (Even (1989 + 1) → a (1989 + 1) = 0) := by exact (lem 1989).right
    ring_nf at cla1 cla2
    
    have : Odd 1989 := by use 994; norm_num
    apply cla1 at this
    have : Even 1990 := by use 995;
    apply cla2 at this
    tauto
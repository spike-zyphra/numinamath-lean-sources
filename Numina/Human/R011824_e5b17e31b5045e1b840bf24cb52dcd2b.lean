import Mathlib

/- Let $n$ be a non-zero natural number, and $n$ the LCM of all integers less than or equal to $m$. Let $\sigma$ also be a permutation of the set $\{1,2, \ldots, n\}$. Show that $\sigma$ is of finite order, and that the order of $\sigma$ divides $m$. -/

theorem number_theory_156878 (n m : ℕ) (σ : Equiv.Perm (Fin n))
    (hm : m = Multiset.lcm (Finset.Icc 1 n).val) : σ ^ m = 1 := by
  -- We prove it by induction on the cycle structure of σ.
  induction' σ using Equiv.Perm.cycle_induction_on with σ hσ τ σ hd hτ htm hsm
  · -- If σ is the identity, then it has order 1, which divides m.
    exact one_pow m
  · -- If σ is a cycle, then its order is the length of the cycle, which divides m.
    rw [← orderOf_dvd_iff_pow_eq_one, Equiv.Perm.IsCycle.orderOf hσ, hm]
    apply Multiset.dvd_lcm
    rw [Finset.mem_val, Finset.mem_Icc, Finset.one_le_card]
    exact ⟨Equiv.Perm.IsCycle.nonempty_support hσ, card_finset_fin_le σ.support⟩
  · -- If σ is a product of disjoint cycles, then by the induction hypothesis, each cycle has order dividing m. They commute with each other, so the m-th power of the product is the product of the m-th powers, which are all the identity.
    rw [Commute.mul_pow (Equiv.Perm.Disjoint.commute hd), htm, hsm, mul_one]
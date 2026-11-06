import Mathlib

/- Let $n$ be an even positive integer. Prove that $\varphi(n) \leq \frac{n}{2}$. -/


theorem number_theory_608885 (n : ℕ) (npos: 0<n) (neven: Even n) : Nat.totient n ≤ n/2 := by

  -- all the integers coprime to n must be odd
  have coptoOdd: ∀ a ∈ Finset.range n, (n.Coprime a) → Odd a := by
    by_contra h; push_neg at h;
    obtain ⟨a, aln, ncopa, aeven⟩ := h; rw[Nat.not_odd_iff_even] at aeven
    rw [Nat.coprime_iff_gcd_eq_one] at ncopa
    have : 2 ∣ n := by exact even_iff_two_dvd.mp neven
    have : 2 ∣ a := by exact even_iff_two_dvd.mp aeven
    have : 2 ∣ n.gcd a := by apply Nat.dvd_gcd; assumption; assumption
    rw [ncopa] at this; omega
  have : {a ∈ Finset.range n | n.Coprime a} ⊆ {a ∈ Finset.range n | Odd a} := by
    intro a; simp; intro aln ncopa
    constructor
    exact aln
    apply coptoOdd; simp; repeat assumption
  have : {a ∈ Finset.range n | n.Coprime a}.card ≤ {a ∈ Finset.range n | Odd a}.card := by exact Finset.card_le_card this

  -- there are at most n/2 odd postitive integers ≤ n
  have : {a ∈ Finset.range n | Odd a}.card ≤ n/2 := by
    let Ao := {a ∈ Finset.range n | Odd a}
    let nf := Finset.range (n/2)
    let f := fun a ↦ (a-1)/2
    have finj: Set.InjOn f Ao := by
      intro a1 ha1 a2 ha2 faeq
      simp [Ao] at ha1; simp [Ao] at ha2;
      simp [f] at faeq;
      have a1Odd : Odd a1 := by exact ha1.right
      have a2Odd: Odd a2 := by exact ha2.right
      have : a1 -1 = (a1 -1) /2 * 2 := by
        refine Eq.symm (Nat.div_two_mul_two_of_even ?_)
        refine Nat.Odd.sub_odd ?_ ?_
        exact a1Odd; simp
      have : a2 -1 = (a2 -1) /2 * 2 := by
        refine Eq.symm (Nat.div_two_mul_two_of_even ?_)
        refine Nat.Odd.sub_odd ?_ ?_
        exact a2Odd; simp
      have : a1-1 = a2-1 := by nlinarith
      have a1pos: 1 ≤ a1 := by refine Nat.one_le_iff_ne_zero.mpr ?_; exact Nat.ne_of_odd_add a1Odd
      have a2pos: 1 ≤ a2 := by refine Nat.one_le_iff_ne_zero.mpr ?_; exact Nat.ne_of_odd_add a2Odd
      exact Nat.sub_one_cancel a1pos a2pos this

    have fima: ∀ a ∈ Ao, f a ∈ nf := by
      intro a ainAo;
      simp [f]; simp [nf]; simp [Ao] at ainAo;
      obtain ⟨aln, odda⟩ := ainAo;
      apply Nat.div_lt_div_of_lt_of_dvd;
      simp [Even] at neven; obtain ⟨r, hr⟩ := neven; rw[← two_mul] at hr; use r; omega

    have _: nf.card = n/2 := by exact Finset.card_range (n / 2)
    have _: Ao.card ≤ nf.card := by exact Finset.card_le_card_of_injOn f fima finj
    linarith

  rw [Nat.totient_eq_card_coprime]
  simp_all; linarith

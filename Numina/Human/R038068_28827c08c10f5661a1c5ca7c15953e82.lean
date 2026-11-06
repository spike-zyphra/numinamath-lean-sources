import Mathlib
open BigOperators Finset

/- (Existence of primitive roots)

Let $p$ be a prime number, $d$ a positive divisor of $p-1$. Show that there are at most $\phi(d)$ elements whose multiplicative order is $d$ modulo $p$. Deduce that there is an element of order exactly $p-1$ modulo $p$. -/
theorem number_theory_113251 (p d : ℕ) (hp : Nat.Prime p) (hpz : NeZero p) (hd : 0 < d)
    (hdd : d ∣ p - 1) :
    #{x : (ZMod p)ˣ | orderOf x = d} ≤ d.totient ∧
    ∃ x : (ZMod p)ˣ, orderOf x = p - 1 := by
  have p_prime : Fact (Nat.Prime p) := { out := hp }
  -- we will show something stronger: that the number of elements of order d' is d'.totient
  suffices : ∀ d' > 0, d' ∣ p - 1 → #{x : (ZMod p)ˣ | orderOf x = d'} ≠ 0 → #{x : (ZMod p)ˣ | orderOf x = d'} = d'.totient
  constructor
  rcases Decidable.eq_or_ne #{x : (ZMod p)ˣ | orderOf x = d} 0 with hz | ho
  · rw [hz]; exact Nat.zero_le _
  exact (this d hd hdd ho).le
  have p_pos : p - 1 > 0 := Nat.zero_lt_sub_of_lt (Nat.Prime.one_lt hp)
  rcases Decidable.eq_or_ne #{x : (ZMod p)ˣ | orderOf x = p - 1} 0 with (hz | ho)
  swap
  · rcases Finset.card_ne_zero.mp ho with ⟨a, ha⟩
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  -- suppose there is no element of order p - 1
  let nz_deg : Finset ℕ := {d' ∈ (p - 1).divisors | ∃ x : (ZMod p)ˣ, orderOf x = d'}
  let f : Function.Embedding nz_deg (Finset (ZMod p)ˣ) := {
    toFun := fun d' ↦ ({x : (ZMod p)ˣ | orderOf x = d'} : Finset _)
    inj' := by
      intro a b hab
      rw [Subtype.ext_iff_val]
      rcases (mem_filter.mp a.2).2 with ⟨x, hx⟩
      dsimp only at hab
      have hx' : x ∈ ({y | orderOf y = b} : Finset _) := by rw [←hab]; simp; exact hx
      simp at hx'
      rw [←hx, ←hx']
  }
  -- partition by the orders of elements
  let P : Finpartition (Finset.univ : Finset (ZMod p)ˣ) := {
    parts := Finset.univ.image f
    supIndep := by
      rw [supIndep_iff_pairwiseDisjoint]; intro s hs t ht hst;
      simp [Function.onFun, disjoint_left]
      simp [f] at hs ht
      rcases hs with ⟨d₁, hd₁, hds⟩
      rcases ht with ⟨d₂, hd₂, hdt⟩
      have hne : d₁ ≠ d₂
      · by_contra he
        apply hst
        rw [←hds, ←hdt]
        ext x
        simp
        rw [he]
      rw [←hds, ←hdt]
      simp
      intro x hx
      calc
        orderOf x = d₁ := hx
        _ ≠ d₂ := hne
    sup_parts := by
      simp only [sup_image, Function.id_comp];
      ext x
      constructor
      intro _; exact mem_univ x
      rw [mem_sup]
      intro hx
      use {
        val := orderOf x
        property := by simp [nz_deg]; exact ⟨ZMod.orderOf_units_dvd_card_sub_one x, p_pos.ne.symm⟩
      }
      constructor
      exact mem_univ _
      simp [f]
    not_bot_mem := by
      simp [f];
      intro d' hd';
      rw [filter_eq_empty_iff];
      push_neg;
      simp [nz_deg] at hd';
      rcases hd'.right with ⟨x, hx⟩;
      exact ⟨x, mem_univ x, hx⟩
  }

  -- sum the sets with order d' and show there are less than p-1 elements, which is a contradiction
  absurd calc
    p - 1
    _ = #(Finset.univ : Finset (ZMod p)ˣ) := by
      exact (ZMod.card_units p).symm
    _ = ∑ p ∈ P.parts, #p := by exact (Finpartition.sum_card_parts P).symm
    _ = ∑ d' ∈ nz_deg, #{x : (ZMod p)ˣ | orderOf x = d'} := by
      unfold P; simp only [EmbeddingLike.apply_eq_iff_eq, imp_self, implies_true, sum_image]
      unfold f; simp only [Function.Embedding.coeFn_mk]
      rw [←Finset.sum_subtype _ _ (fun d' ↦ #{x | orderOf x = d'})]
      intro _; exact Eq.to_iff rfl
    _ = ∑ d' ∈ nz_deg, d'.totient := by
      apply Finset.sum_congr rfl _
      intro d' hd'
      rw [mem_filter, Nat.mem_divisors] at hd'
      apply this d' (Nat.pos_of_dvd_of_pos hd'.1.1 p_pos) hd'.1.1
      apply Finset.card_ne_zero.mpr
      rcases hd'.2 with ⟨x, hx⟩
      use x; simp; exact hx
    _ < ∑ d' ∈ (p - 1).divisors, d'.totient := by
      have st_subset : nz_deg ⊆ (p - 1).divisors :=
        fun d' hd' ↦ (mem_filter.mp hd').1
      have p1 : p - 1 ∈ (p - 1).divisors := by apply Nat.mem_divisors.mpr; exact ⟨Nat.dvd_refl _, p_pos.ne.symm⟩
      apply Finset.sum_lt_sum_of_subset st_subset p1
      simp [nz_deg]
      intro _ x
      exact card_filter_eq_zero_iff.mp hz x (mem_univ x)
      exact Nat.totient_pos.mpr p_pos
      intro d' hd' hd''
      exact Nat.zero_le _
    _ = p - 1 := by exact Nat.sum_totient _
  exact Nat.lt_irrefl _
  clear hd hdd d

  -- to show that the number of elements of order d' is d'.totient, we proceed by induction
  intro d hd hdd h_nonemp
  induction' d using Nat.strongRec with d ih
  rcases Finset.card_ne_zero.mp h_nonemp with ⟨a, ha⟩
  simp only [mem_filter, mem_univ, true_and] at ha

  have h1 : ∑ m ∈ d.properDivisors, #{x : (ZMod p)ˣ | orderOf x = m} = ∑ m ∈ d.properDivisors, m.totient
  · have : ∀ m ∈ d.properDivisors, #{x : (ZMod p)ˣ | orderOf x = m} = m.totient
    · intro m hm
      rw [Nat.mem_properDivisors] at hm
      apply ih m hm.2 (Nat.pos_of_dvd_of_pos hm.1 hd) (hm.1.trans hdd)
      apply Finset.card_ne_zero.mpr
      use a^(d / m)
      simp only [mem_filter, mem_univ, true_and]
      rw [orderOf_pow' a, ha, Nat.gcd_eq_right (Nat.div_dvd_of_dvd hm.1), Nat.div_div_self hm.1 hd.ne.symm]
      exact (Nat.div_ne_zero_iff_of_dvd hm.1).mpr ⟨hd.ne.symm, (Nat.pos_of_dvd_of_pos hm.1 hd).ne.symm⟩
    exact_mod_cast Finset.sum_congr rfl this

  have aux : #{b : (ZMod p)ˣ | b ^ orderOf a = 1} = orderOf a
  · apply le_antisymm
    apply IsCyclic.card_pow_eq_one_le (orderOf_pos a)
    calc
      orderOf a = Fintype.card (Subgroup.zpowers a) := by exact Fintype.card_zpowers.symm
      _ ≤ Fintype.card ({b : (ZMod p)ˣ | b ^ orderOf a = 1}) := by
        apply Fintype.card_le_of_injective (id _) (id _)
        intro b; exact {
          val := b.1,
          property := by let ⟨i, hi⟩ := b.2; rw [Set.mem_setOf_eq, ←hi, ←zpow_natCast, ←zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
        }
        intro _ _ h; exact Subtype.eq (Subtype.mk.inj h)
      _ = #{b : (ZMod p)ˣ | b ^ orderOf a = 1} := Fintype.card_ofFinset _ _
  have patch : ∑ m in d.divisors, #{x : (ZMod p)ˣ | orderOf x = m} = #{x : (ZMod p)ˣ | x^d = 1}
  · convert sum_card_orderOf_eq_card_pow_eq_one hd.ne.symm
    exact (Nat.filter_dvd_eq_divisors hd.ne.symm).symm
  have h2 : ∑ m ∈ d.divisors, #{x : (ZMod p)ˣ | orderOf x = m} = ∑ m ∈ d.divisors, m.totient
  · rw [patch, Nat.sum_totient, ←ha, aux]
  rw [←Nat.cons_self_properDivisors hd.ne.symm, sum_cons, sum_cons, h1] at h2
  linarith
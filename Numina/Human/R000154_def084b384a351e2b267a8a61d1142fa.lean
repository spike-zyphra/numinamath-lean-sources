import Mathlib

/- Theorem 8.5 states that if a positive integer \( m \) has a primitive root, then it has a total of \( \phi(\phi(m)) \) incongruent primitive roots.-/
theorem number_theory_4990 (m : ℕ) (hm : 0 < m) (PR : IsCyclic (ZMod m)ˣ) :
    {x : (ZMod m)ˣ | orderOf x = m.totient}.ncard = (m.totient).totient := by
  --we prove that if m has a primitive root, then it has a total of (m.totient).totient incongruent primitive roots.
  --pick a generator of the unit group by assumption
  rcases PR with ⟨t, ht⟩
  have r0 : NeZero m := by
    apply neZero_iff.mpr; linarith
  -- the generator has order m.totient
  have r1 : orderOf t = m.totient := by
    rw [← ZMod.card_units_eq_totient m]
    convert orderOf_eq_card_of_forall_mem_zpowers ht
    simp
  have r2 := Nat.totient_pos.mpr hm
  have r5 : NeZero m.totient := by
    apply neZero_iff.mpr; linarith

  --construct a map f from the set of numbers less than m.totient that are coprime to m.totient, to the unit group
  let f : Finset.filter (Nat.Coprime (Nat.totient m)) (Finset.range (Nat.totient m)) → (ZMod m)ˣ :=
  fun i => t ^ (i.val)

  --show that the range of f is the set of incongruent primitive roots
  have range_f : f '' Set.univ = {x : (ZMod m)ˣ | orderOf x = m.totient} := by
    simp; apply (Set.range_eq_iff f {x : (ZMod m)ˣ | orderOf x = m.totient}).mpr
    constructor; simp only [f]; simp; intro a _ ha2
    rw [Nat.coprime_iff_gcd_eq_one] at ha2
    rw [orderOf_pow, r1, ha2]; simp
    simp only [f]; simp; intro b hb
    have t2 := ht b
    rcases t2 with ⟨k, hk⟩; simp at hk
    use ZMod.val (k : (ZMod m.totient));
    have t3 : t ^ k = t ^ (ZMod.val (k : ZMod m.totient)) := by
      rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, r1, ZMod.val_intCast]
      rw [Int.modEq_comm]; exact Int.mod_modEq k ↑(Nat.totient m)
    constructor; constructor;
    · exact ZMod.val_lt (k : (ZMod m.totient))
    · rw [hk] at t3; rw [t3, orderOf_pow, r1] at hb
      apply Nat.div_eq_self.mp at hb
      cases hb with
      | inl hll => linarith
      | inr hrr => rw [Nat.coprime_iff_gcd_eq_one]; exact hrr
    · rw [t3] at hk; exact hk

  --show that f is injective
  have inj_f : Function.Injective f := by
    rw [Function.Injective]; simp only [f]; simp
    intro a1 ha1 _ a2 ha2 _ h12
    rw [pow_eq_pow_iff_modEq, r1] at h12
    have u1 := Nat.mod_eq_of_modEq h12 ha2
    have u2 := Nat.mod_eq_of_lt ha1
    rw [u1] at u2; exact symm u2

  --apply the lemma that says injective maps preserve Set.ncard between the image set and the domain
  have r4 := Set.ncard_image_of_injective Set.univ inj_f
  rw [range_f, Set.ncard_univ, Nat.card_eq_finsetCard (Finset.filter (Nat.Coprime (Nat.totient m)) (Finset.range (Nat.totient m)))] at r4
  rw [Nat.totient_eq_card_coprime (Nat.totient m)]; exact r4

import Mathlib

/- we first prove a lemma that the unit group of ZMod p is cyclic-/
lemma CycZModp (p : ℕ) [inst : Fact (Nat.Prime p)] : IsCyclic (ZMod p)ˣ := by
  let UtoR : OneHom (ZMod p)ˣ (ZMod p) := OneHom.mk Units.val Units.val_one
  have UtoRmul : ∀ (x y : (ZMod p)ˣ), UtoR.toFun (x * y) = UtoR.toFun x * UtoR.toFun y := Units.val_mul
  let UtoRmor : (ZMod p)ˣ →* ZMod p := MonoidHom.mk UtoR UtoRmul
  have : Function.Injective UtoRmor := by
    rw [Function.Injective]; intro x y; simp only [UtoRmor]; simp
    intro hxy; simp only [UtoR] at hxy; simp at hxy
    exact Units.eq_iff.mp hxy
  apply isCyclic_of_subgroup_isDomain UtoRmor this

/- Theorem 8.7 states that if \( p \) is a prime number and \( d \) is a positive divisor of \( p-1 \), then the number of incongruent integers of order \( d \) modulo \( p \) is equal to \( \phi(d) \), where \( \phi \) is the Euler's totient function.-/
theorem number_theory_5013 (p d : ℕ) [inst : Fact (Nat.Prime p)] (hd1 : d ∣ p - 1) (hd2 : d ≠ 0) :
    {x : (ZMod p)ˣ | orderOf x = d}.ncard = d.totient := by
  --apply the lemma and pick a generator for the unit group
  rcases CycZModp p with ⟨t, ht⟩
  --prove the generator has order p-1
  have r2 : orderOf t = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht]
    simp; exact Nat.totient_prime inst.1
  --prepare some simple inequalities for later use
  have r3 : 0 < p - 1 := by
    have t1 := (Nat.prime_def_lt.mp inst.1).left
    have : 1 < p := by linarith
    rw [Nat.sub_pos_iff_lt]; exact this

  rcases hd1 with ⟨e, he⟩; symm at he

  have r4 : 0 < e := by
    by_contra h''; push_neg at h''
    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith

  have r6 : 0 < d := by
    by_contra h''; push_neg at h''
    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
  --write out an equivalent form of the order of an element
  have r5 := (orderOf_eq_iff r3).mp r2
  --construct a function f from the set of numbers less than d that are coprime with d, to the unit group
  let f : Finset.filter (Nat.Coprime d) (Finset.range d) → (ZMod p)ˣ := fun i => t ^ (e * i.val)
  --prove that the range of f is the set of incongruent integers of order d modulo p
  have range_f : f '' Set.univ = {x : (ZMod p)ˣ | orderOf x = d} := by
    simp; apply (Set.range_eq_iff f {x : (ZMod p)ˣ | orderOf x = d}).mpr
    constructor; intro a; simp; simp only [f]
    rw [orderOf_pow, r2, ← he]; nth_rw 3 [mul_comm]
    rw [Nat.gcd_mul_right, Nat.mul_div_mul_right]
    have t1 := a.2
    simp only [Finset.mem_filter, Finset.mem_range] at t1; rw [Nat.coprime_iff_gcd_eq_one] at t1
    rw [t1.right]; simp; exact r4
    simp only [f]; simp; intro b hb
    have t2 := ht b
    rcases t2 with ⟨k, hk⟩; simp at hk
    have t4 := (orderOf_eq_iff r6).mp hb; rcases t4 with ⟨hb1, _⟩
    rw [← hk, ← zpow_natCast, ← zpow_mul, ← orderOf_dvd_iff_zpow_eq_one, r2] at hb1
    rcases hb1 with ⟨w, hw⟩; rw [← he, mul_comm] at hw; simp at hw
    rw [mul_assoc] at hw; apply mul_left_cancel₀ at hw
    have t3 : NeZero d := neZero_iff.mpr hd2
    use ZMod.val (w : ZMod d)
    have t4 : (t ^ e) ^ (ZMod.val (w : ZMod d)) = b := by
      rw [symm hk, ← pow_mul, ← zpow_natCast, zpow_eq_zpow_iff_modEq, hw]
      rw [r2, ← he, Int.modEq_iff_add_fac]
      have : (d : ℤ) ∣ (w - ZMod.val (w : ZMod d)) := by
        rw [ZMod.val_intCast, Int.emod_def]; simp
      rcases this with ⟨v, hv⟩; use v; simp only [Nat.cast_mul]
      ring_nf; rw [mul_assoc, ← mul_add]
      have : 0 < (e : ℤ) := by linarith
      apply (mul_left_cancel_iff_of_pos this).mpr
      rw [symm hv]; simp

    have t5 : orderOf (t ^ e) = d := by
      rw [orderOf_pow, r2, ← he]; simp
      rw [Nat.mul_div_cancel]; exact r4
    constructor; constructor
    exact ZMod.val_lt (w : ZMod d); rw [hw, zpow_mul, zpow_natCast] at hk
    rw [← t4, orderOf_pow, t5, Nat.div_eq_self] at hb
    cases hb with
    | inl hll => linarith
    | inr hrr => rw [Nat.coprime_iff_gcd_eq_one]; exact hrr
    rw [pow_mul]; exact t4; linarith
  --prove that f is injective
  have inj_f : Function.Injective f := by
    rw [Function.Injective]; simp only [f]; simp
    intro a1 ha1 h'a1 a2 ha2 h'a2 h12
    by_contra hne; push_neg at hne; rw [Nat.ne_iff_lt_or_gt] at hne
    cases hne with
    | inl hll =>
                have : a1 ≤ a2 := by linarith
                have u1 := Nat.add_sub_cancel' this
                rw [← u1, Nat.mul_add, pow_add] at h12; symm at h12
                rw [mul_right_eq_self] at h12
                have u2 : e * (a2 - a1) < p - 1 := by
                  have v1: a2 - a1 ≤ a2 := by linarith
                  have v2 := Nat.lt_of_le_of_lt v1 ha2
                  have v3 : 0 < e := by
                    by_contra h''; push_neg at h''
                    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  rw [← he]; nth_rw 2 [mul_comm]; rw [Nat.mul_lt_mul_left v3]
                  exact v2
                have u4 : 0 < e * (a2 - a1) := by
                  apply Nat.mul_pos; by_contra h''; push_neg at h''
                  rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  linarith
                have u3 := r5.right (e * (a2 - a1)) u2 u4
                contradiction
    | inr hrr =>
                have : a2 ≤ a1 := by linarith
                have u1 := Nat.add_sub_cancel' this
                rw [← u1, Nat.mul_add, pow_add, mul_right_eq_self] at h12
                have u2 : e * (a1 - a2) < p - 1 := by
                  have v1: a1 - a2 ≤ a1 := by linarith
                  have v2 := Nat.lt_of_le_of_lt v1 ha1
                  have v3 : 0 < e := by
                    by_contra h''; push_neg at h''
                    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  rw [← he]; nth_rw 2 [mul_comm]; rw [Nat.mul_lt_mul_left v3]
                  exact v2
                have u4 : 0 < e * (a1 - a2) := by
                  apply Nat.mul_pos; by_contra h''; push_neg at h''
                  rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  linarith
                have u3 := r5.right (e * (a1 - a2)) u2 u4
                contradiction
  --apply the lemma that says injective functions preserves Set.ncard between the image and the domain
  have r1 := Set.ncard_image_of_injective Set.univ inj_f
  rw [range_f, Set.ncard_univ, Nat.card_eq_finsetCard (Finset.filter (Nat.Coprime d) (Finset.range d))] at r1
  rw [Nat.totient_eq_card_coprime d]; exact r1

import Mathlib

set_option maxHeartbeats 400000

/- the lemma proves that the unit group of ZMod p is cyclic -/
lemma CycZModp (p : ℕ) [inst : Fact (Nat.Prime p)] : IsCyclic (ZMod p)ˣ := by
  let UtoR : OneHom (ZMod p)ˣ (ZMod p) := OneHom.mk Units.val Units.val_one
  have UtoRmul : ∀ (x y : (ZMod p)ˣ), UtoR.toFun (x * y) = UtoR.toFun x * UtoR.toFun y := Units.val_mul
  let UtoRmor : (ZMod p)ˣ →* ZMod p := MonoidHom.mk UtoR UtoRmul
  have : Function.Injective UtoRmor := by
    rw [Function.Injective]; intro x y; simp only [UtoRmor]; simp
    intro hxy; simp only [UtoR] at hxy; simp at hxy
    exact Units.eq_iff.mp hxy
  apply isCyclic_of_subgroup_isDomain UtoRmor this

/- Theorem 8.6 states that if \( p \) is a prime number and \( d \) is a divisor of \( p-1 \), then the polynomial \( x^{d}-1 \) has exactly \( d \) incongruent roots modulo \( p \).-/
theorem number_theory_5012 (p d : ℕ) [inst : Fact (Nat.Prime p)] (hd1 : d ∣ p - 1) (hd2 : 0 < d) :
    {x : (ZMod p)ˣ | x ^ d = 1}.ncard = d := by
  --Apply lemma and pick a generator for the cyclic group
  rcases CycZModp p with ⟨t, ht⟩
  --Show that the order of the generator is p - 1
  have r2 : orderOf t = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ht]
    simp; exact Nat.totient_prime inst.1
  --Prepare a simple inequality for later use
  have r3 : 0 < p - 1 := by
    have t1 := (Nat.prime_def_lt.mp inst.1).left
    have : 1 < p := by linarith
    rw [Nat.sub_pos_iff_lt]; exact this
  --Write out the equivalent form of the order of an element
  have r4 := (orderOf_eq_iff r3).mp r2
  --Construct a function from Finset.range d to (ZMod p)ˣ
  rcases hd1 with ⟨e, he⟩; symm at he
  let f : Finset.range d → (ZMod p)ˣ := fun i => t ^ (e * i)
  --Show that the range of f is {x : (ZMod p)ˣ | x ^ d = 1}
  have range_f : f '' Set.univ = {x : (ZMod p)ˣ | x ^ d = 1} := by
    simp; apply (Set.range_eq_iff f {x : (ZMod p)ˣ | x ^ d = 1}).mpr
    constructor; intro a; simp; simp only [f]
    rw [← pow_mul, mul_comm,← mul_assoc, he, pow_mul, r4.left]; simp
    intro b hb; simp at hb; simp only [f]
    have t1 := ht b
    rcases t1 with ⟨k, hk⟩;
    rw [← hk, ← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_modEq, r2, Int.ModEq] at hb
    simp at hb; rcases hb with ⟨i, hi⟩
    rw [symm he, mul_comm] at hi; simp at hi; rw [mul_assoc] at hi
    apply mul_left_cancel₀ at hi
    simp; use ZMod.val (i : ZMod d)
    have t4: NeZero d := by
      rw [neZero_iff]; linarith
    constructor; exact ZMod.val_lt (i : ZMod d)
    rw [← hk, ← zpow_natCast, zpow_eq_zpow_iff_modEq, r2, Int.modEq_iff_add_fac]
    have t5 : (d : ℤ) ∣ i - (ZMod.val (i : ZMod d)) := by
      apply Int.modEq_iff_dvd.mp; rw [ZMod.val_intCast]
      apply Int.mod_modEq
    rcases t5 with ⟨t, ht⟩; use t
    rw [symm he, hi]; simp; ring_nf; rw [mul_assoc, ← mul_add]
    have t2 : (e : ℤ) ≠ 0 := by
      intro h'e; simp at h'e; rw [h'e] at he; simp at he; linarith
    apply (Int.mul_eq_mul_left_iff t2).mpr; rw [← ht]; simp
    linarith

  --Show that f is injective
  have inj_f : Function.Injective f := by
    rw [Function.Injective]; simp only [f]; simp; intro i hi j hj hij
    by_contra hne; push_neg at hne; rw [Nat.ne_iff_lt_or_gt] at hne
    cases hne with
    | inl hll =>
                have : i ≤ j := by linarith
                have u1 := Nat.add_sub_cancel' this
                rw [← u1, Nat.mul_add, pow_add] at hij; symm at hij
                rw [mul_right_eq_self] at hij
                have u2 : e * (j - i) < p - 1 := by
                  have v1: j - i ≤ j := by linarith
                  have v2 := Nat.lt_of_le_of_lt v1 hj
                  have v3 : 0 < e := by
                    by_contra h''; push_neg at h''
                    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  rw [← he]; nth_rw 2 [mul_comm]; rw [Nat.mul_lt_mul_left v3]
                  exact v2
                have u4 : 0 < e * (j - i) := by
                  apply Nat.mul_pos; by_contra h''; push_neg at h''
                  rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  linarith
                have u3 := r4.right (e * (j - i)) u2 u4
                contradiction
    | inr hrr =>
                have : j ≤ i := by linarith
                have u1 := Nat.add_sub_cancel' this
                rw [← u1, Nat.mul_add, pow_add, mul_right_eq_self] at hij
                have u2 : e * (i - j) < p - 1 := by
                  have v1: i - j ≤ i := by linarith
                  have v2 := Nat.lt_of_le_of_lt v1 hi
                  have v3 : 0 < e := by
                    by_contra h''; push_neg at h''
                    rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  rw [← he]; nth_rw 2 [mul_comm]; rw [Nat.mul_lt_mul_left v3]
                  exact v2
                have u4 : 0 < e * (i - j) := by
                  apply Nat.mul_pos; by_contra h''; push_neg at h''
                  rw [Nat.le_zero] at h''; rw [h''] at he; simp at he; linarith
                  linarith
                have u3 := r4.right (e * (i - j)) u2 u4
                contradiction

  --Apply the lemma that says injective functions preserve Set.ncard between the image and the domain
  have r1 := Set.ncard_image_of_injective Set.univ inj_f
  rw [range_f, Set.ncard_univ, Nat.card_eq_finsetCard (Finset.range d)] at r1
  simp at r1; exact r1

import Mathlib

namespace number_theory_95271

noncomputable def is_p_safe (p n : ℕ) := ∀ m : ℤ, ↑p ∣ m → Int.natAbs (n - m : ℤ) > 2

end number_theory_95271

/- For a positive integer $p$, define the positive integer $n$ to be $p$-safe if $n$ differs in absolute value by more than $2$ from all multiples of $p$. For example, the set of $10$-safe numbers is $\{ 3, 4, 5, 6, 7, 13, 14, 15, 16, 17, 23, \ldots\}$. Find the number of positive integers less than or equal to $10,000$ which are simultaneously $7$-safe, $11$-safe, and $13$-safe. -/
theorem number_theory_95271 :
    Set.ncard {n | 0 < n ∧ n ≤ 10000 ∧ number_theory_95271.is_p_safe 7 n ∧ number_theory_95271.is_p_safe 11 n ∧ number_theory_95271.is_p_safe 13 n} = 958 := by

  -- We see that a number is p-safe if and only if its residue mod p is not in [-2, 2].
  let p_safe_residues (p : ℕ) [NeZero p] : Finset (ZMod p) :=
    (Finset.image (fun (z : ℤ) => (z : ZMod p)) (Finset.Icc (-2) 2))ᶜ

  have p_safe_residues_iff {p n : ℕ} [NeZero p] (hp : 5 ≤ p) : number_theory_95271.is_p_safe p n ↔ (n : ZMod p) ∈ p_safe_residues p := by
    simp [number_theory_95271.is_p_safe, p_safe_residues, -and_imp]
    constructor
    . intro f z ⟨hzl, hzr⟩ hz
      have : (z : ZMod p) = (n : ℤ) := by simp [hz]
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at this
      obtain ⟨c, pc⟩ := this
      have := f (p * c) (Dvd.intro c rfl)
      rw [show n - p * c = z by linarith] at this
      omega
    . intro hn m hm
      rcases le_or_gt (Int.natAbs ((n : ℤ) - (m : ℤ))) 2 with h | h
      . exfalso
        have : ((n - m : ℤ) : ZMod p) ≠ (n : ZMod p) := hn (n - m : ℤ) (by omega)
        simp at this
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hm
        exact this hm
      . exact h

  -- If p ≤ 5, all the residue classes {-2, ..., 2} are distinct so the set of p-safe residues has size p - 5.
  have p_safe_residues_card {p : ℕ} [NeZero p] (hp : 5 ≤ p := by norm_num) : (p_safe_residues p).card = p - 5 := by
    suffices : (Finset.image (fun (z : ℤ) => (z : ZMod p)) (Finset.Icc (-2) 2)).card = 5
    . simp [p_safe_residues]
      rw [eq_comm, Nat.sub_eq_iff_eq_add' hp, ← this, Finset.card_add_card_compl]
      simp
    apply Finset.card_image_of_injOn
    simp
    rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩ h
    simp at h
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
    have : y - x = 0 := by
      refine Int.eq_zero_of_abs_lt_dvd h ?_
      rw [Int.abs_eq_natAbs]
      omega
    linarith

  -- This version of is_p_safe is decidable, so we can rewrite our target set as a Finset to make computing
  -- the cardinality easier.
  simp_rw [p_safe_residues_iff (show 5 ≤ 7 by norm_num), p_safe_residues_iff (show 5 ≤ 11 by norm_num), p_safe_residues_iff (show 5 ≤ 13 by norm_num)]
  have : {n : ℕ | 0 < n ∧ n ≤ 10000 ∧ ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13} =
      {n ∈ Finset.Ioc (0 : ℕ) 10000 | ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13} := by
    ext n
    simp
    rw [and_assoc]
  rw [this, Set.ncard_coe_Finset]

  -- Now since 7, 11, and 13 are all coprime, by the Chinese Remainder Theorem a number's residue mod 1001
  -- uniquely determines its residues mod 7, 11, and 13. Since 1001 * 10 = 10010 is very close to 10000, we
  -- can compute the number of 7-safe, 11-safe, and 13-safe numbers less than 10010 and then handle the
  -- stragglers separately.

  have : Disjoint (Finset.Ioc 0 10000) ({0} ∪ Finset.Ioo 10000 10010) := by
    rw [Finset.disjoint_iff_ne]
    simp
    intro a h1 h2
    and_intros
    . linarith
    . intro a' h1' h2'
      linarith

  have hunion : Finset.range 10010 = Finset.disjUnion (Finset.Ioc 0 10000) ({0} ∪ Finset.Ioo 10000 10010) this := by
    ext n
    simp
    omega

  suffices : {n ∈ Finset.range 10010 | ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13}.card =
    958 + {n ∈ {0} ∪ Finset.Ioo (10000 : ℕ) 10010 | ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13}.card
  . rw [hunion, Finset.filter_disj_union, Finset.card_disjUnion] at this
    linarith

  -- We can compose a bunch of equivalences to show that n ↦ (n / 1001, n mod 7, n mod 11, n mod 13) is indeed
  -- an equivalence.
  let e : ℕ ≃ ℕ × ZMod 7 × ZMod 11 × ZMod 13 := by
    refine Equiv.trans (Nat.divModEquiv 1001) ?_
    refine Equiv.prodCongr (Equiv.refl _) ?_
    refine Equiv.trans (ZMod.finEquiv _).toEquiv ?_
    refine Equiv.trans (ZMod.chineseRemainder (show Nat.Coprime 7 143 by norm_num)).toEquiv ?_
    refine Equiv.prodCongr (Equiv.refl _) ?_
    exact (ZMod.chineseRemainder (show Nat.Coprime 11 13 by norm_num)).toEquiv

  -- And we verify that this equivalence is the right function.
  have e_apply {n} : e n = (n / 1001, (↑n, ↑n, ↑n)) := by
    have : CharP (ZMod 11 × ZMod 13) 143 := Nat.lcm.charP _ _ 11 13
    have : CharP (ZMod 7 × ZMod 143) 1001 := Nat.lcm.charP _ _ 7 143
    simp [e]
    ext <;> simp

  -- Now, on the range 0 to 10010, we can compute the target cardinality as a product.
  let S : Finset (ℕ × ZMod 7 × ZMod 11 × ZMod 13) := Finset.range 10 ×ˢ p_safe_residues 7 ×ˢ p_safe_residues 11 ×ˢ p_safe_residues 13
  have : Set.BijOn e {n ∈ Finset.range 10010 | ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13} S := by
    refine Equiv.bijOn e ?_
    intro n
    simp [e_apply, S, p_safe_residues_iff, Nat.div_lt_iff_lt_mul]

  have : {n ∈ Finset.range 10010 | ↑n ∈ p_safe_residues 7 ∧ ↑n ∈ p_safe_residues 11 ∧ ↑n ∈ p_safe_residues 13}.card = 960 := by
    rw [← Set.ncard_coe_Finset, ← Set.ncard_image_of_injective _ (Equiv.injective e), Finset.coe_filter, Set.BijOn.image_eq this, Set.ncard_coe_Finset]
    simp [S, p_safe_residues_card]

  rw [this]

  -- For the remaining 10 values, we can check each one individually.
  decide
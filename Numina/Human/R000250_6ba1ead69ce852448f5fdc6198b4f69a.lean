import Mathlib
import Aesop

open BigOperators Real Topology Rat

/-We will need the following lemma on division relations-/
lemma lem : ∀ (v : ℤ), ¬ (8 ∣ v ^ 2 - 5) := by
-- Introduce the variable $v$ and the division assumption
  intro v hv
-- Apply division with remainder on $v$
  have d8 := Int.emod_add_ediv v 8
-- Prove that the remainder is less than $8$
  have r8bpbd := @Int.emod_lt_of_pos v 8 (show (0:ℤ)<8 by norm_num)
  have r8lwbd := Int.emod_nonneg v (show (8:ℤ)≠0 by norm_num)
-- Split the goal to $8$ cases with respect to the remainder modulo $8$
  interval_cases (v % 8)
  all_goals simp_all; rw [← d8] at hv; ring_nf at hv; rw [dvd_add_left] at hv
  contradiction; rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

  rw [dvd_add_left] at hv; contradiction
  rw [dvd_mul]; use 1; use 8; simp; norm_num
  rw [dvd_mul]; use 1; use 8; simp; norm_num

/-For a positive integer  $m$ , prove that the number of pairs of positive integers  $(x,y)$  which satisfies the following two conditions is even or  $0$ .

(i):  $x^2-3y^2+2=16m$ (ii):  $2y \le x-1$-/
theorem number_theory_8699 (m : ℕ) (S : Set (ℤ × ℤ))
(_ : 0 < m) (hS : S = {p : ℤ × ℤ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ^ 2 - 3 * p.2 ^ 2 + 2 = 16 * m ∧ 2 * p.2 ≤ p.1 - 1}):
Even (Nat.card S) ∨ Nat.card S = 0 := by
-- Prove by cases $Nat.card S$ is zero or not
  by_cases hem : Nat.card S = 0
  · right; assumption
-- If $Nat.card S$ is not zero, prove it is even. First we prove that $S$ is finite
  left; push_neg at hem; apply Nat.pos_iff_ne_zero.mpr at hem
  apply Nat.card_pos_iff.mp at hem
  have r0 : S.Finite := by
    apply Set.finite_coe_iff.mp; exact hem.right
  have r'0 : Fintype S := by
    have := Set.finite_coe_iff.mpr r0
    apply Fintype.ofFinite
-- Define a function $F$ on $ℤ×ℤ$
  let F : ℤ × ℤ → ℤ × ℤ := fun p => (2 * p.1 - 3 * p.2, p.1 - 2 * p.2)
-- Prove that $F$ is the inverse of itself
  have r1 : ∀ p, F (F p) = p := by intro p; simp [F]; ring_nf
-- Prove that $F$ maps $S$ to $S$
  have r2 : F ⁻¹' S = S := by
    ext x; constructor
    · simp; nth_rw 2 [← r1 x];
      let (y1, y2) := F x
      rw [hS]; simp; intro _ hy2 hy3 hy4
      constructor
      · rw [show (3:ℤ)=1+2 by norm_num, add_mul, one_mul]
        linarith
      constructor
      · linarith
      constructor
      · ring_nf; rw [add_comm, mul_comm, hy3]; ring
      ring_nf; rw [add_comm, sub_add, sub_neg_eq_add]
      rw [sub_le_sub_iff_left, show (4:ℤ)=3+1 by norm_num, mul_add]
      rw [add_le_add_iff_left]; linarith
    rw [hS]; simp; intro _ hx2 hx3 hx4
    constructor
    · rw [show (3:ℤ)=1+2 by norm_num, add_mul, one_mul]
      linarith
    constructor
    · linarith
    constructor
    · ring_nf; rw [add_comm, mul_comm, hx3]; ring
    ring_nf; rw [add_comm, sub_add, sub_neg_eq_add]
    rw [sub_le_sub_iff_left, show (4:ℤ)=3+1 by norm_num, mul_add]
    rw [add_le_add_iff_left]; linarith
-- Restrict the function $F$ to $S$ and denote the restricted function by $g$
  have r'2 : @Set.Elem (ℤ × ℤ) S = @Set.Elem (ℤ × ℤ) (F ⁻¹' S) := by
    rw [Set.Elem, Set.Elem]; simp [r2]
  let g (c : S) : S := Set.restrictPreimage S F (cast r'2 c)
  have r8 : ∀ y, (g y).val = F (y.val) := by
    intro y; simp [g]; congr; simp
  have r4 : ∀ b, g (g b) = b := by
    intro b; apply Subtype.val_inj.mp
    have := r8 (g b)
    rw [this, r8 b]; exact r1 b
-- Prepare some simple facts for later use
  have t2 : (1 : ZMod 2) ≠ 0 := by simp
  have t3 := (Nat.card_eq_two_iff' (0 : ZMod 2)).mp (show Nat.card (ZMod 2) = 2 by simp)
  rcases t3 with ⟨t, _, ht2⟩; simp at ht2; push_neg at ht2
  have t'2 := ht2 1 t2
  rw [← t'2] at ht2
  have t4 : ∀ t : Multiplicative (ZMod 2), t = Multiplicative.ofAdd (Multiplicative.toAdd t) := @ofAdd_toAdd (ZMod 2)
-- Prove that $g$ does not fix any element in $S$
  have t5 : ∀ b : S, b ≠ g b := by
    intro b hb; apply Subtype.val_inj.mpr at hb
    rw [r8 b, Prod.ext_iff] at hb; simp [F] at hb
    rcases hb with ⟨hb1, hb2⟩
    rw [show (2:ℤ)=1+1 by norm_num, add_mul, add_sub_assoc] at hb1
    simp at hb1; rw [sub_eq_zero] at hb1
    have h'b := b.2
    simp [hS] at h'b; rcases h'b with ⟨_, _, h'b3, h'b4⟩
    rw [hb1] at h'b3; ring_nf at h'b3
    nth_rw 1 [show (2:ℤ)=1*2 by norm_num] at h'b3
    rw [show (6:ℤ)=3*2 by norm_num, ← mul_assoc] at h'b3
    rw [show (16:ℤ)=8*2 by norm_num, ← mul_assoc] at h'b3
    rw [← add_mul] at h'b3; simp at h'b3
    have hdvd : 8 ∣ 3 * ((b:ℤ×ℤ).2 ^ 2 - 5) := by
      use m-2; ring_nf; rw [← h'b3]; ring
    apply Int.dvd_of_dvd_mul_right_of_gcd_one at hdvd
    replace hdvd := hdvd (show (Int.gcd 8 3 = 1) by norm_num)
    have hndvd := lem ((b:ℤ×ℤ).2)
    contradiction
-- Define a group action of the cyclic group of order two on $S$ via $g$
  let act : ZMod 2 → ↑S → ↑S := fun
  | 0, a => a
  | 1, a => g a
  have r3 : ∀ b : ↑S, act 0 b = b := by intro b; simp [act]
-- Define the scalar multiplication structure on $S$
  let toSMul : SMul (Multiplicative (ZMod 2)) ↑S := SMul.mk act
-- Prove the rule of multiplication by $1$
  have one_smul : ∀ (b : ↑S),  (1 : Multiplicative (ZMod 2)) • b = b := r3
-- Prove the associativity law of scalar multiplication
  have mul_smul : ∀ (x y : Multiplicative (ZMod 2)) (b : ↑S), (x * y) • b = x • y • b := by
    intro x y b; by_cases h' : x = 1
    · rw [h']; simp; symm ; exact one_smul (y • b)
    by_cases h'' : y = 1
    · rw [h'', one_smul b]; simp
    have t1 : x * y = 1 := by
      have o1 : x = Multiplicative.ofAdd 1 := by
        by_cases h'x : Multiplicative.toAdd x ≠ 0
        · have xx1 := ht2 (Multiplicative.toAdd x) h'x
          have xx3 := t4 x
          rw [xx1] at xx3; assumption
        push_neg at h'x
        have := t4 x
        rw [h'x] at this; simp at this; contradiction
      have o2 : y = Multiplicative.ofAdd 1 := by
        by_cases h'y : Multiplicative.toAdd y ≠ 0
        · have yy1 := ht2 (Multiplicative.toAdd y) h'y
          have yy3 := t4 y
          rw [yy3] at yy3; assumption
        push_neg at h'y
        have := t4 y
        rw [h'y] at this; simp at this; contradiction
      rw [o1, o2, ← ofAdd_add]; reduce_mod_char; simp
    rw [t1, one_smul b]; simp [HSMul.hSMul, SMul.smul, act]
    split
    · split
      · rfl
      contradiction
    split
    · contradiction
    symm; exact r4 b
-- Define the group action
  let GpAct : MulAction (Multiplicative (ZMod 2)) ↑S := MulAction.mk one_smul mul_smul
-- Prove that any stabilizer group of this group action is trivial
  have r5 : ∀ b : S, MulAction.stabilizer (Multiplicative (ZMod 2)) b = ⊥ := by
    intro b; ext x; rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
    constructor
    · intro hx; by_contra h'x; push_neg at h'x
      have xx1: Multiplicative.toAdd x = 1 := by
        apply ht2; by_contra h''x
        have := t4 x
        rw [h''x] at this; simp at this; contradiction
      have xx2 := t4 x
      have xx3 : x • b = g b := by
        simp [HSMul.hSMul, SMul.smul, act]; split
        · have : @OfNat.ofNat (Fin 2) 0 Fin.instOfNat = @OfNat.ofNat (Multiplicative (ZMod 2)) 1 One.toOfNat1 := rfl
          contradiction
        rfl
      rw [xx3] at hx
      have := t5 b
      symm at this; contradiction
    intro hx; rw [hx]; simp
-- Prove that the quotient of this group action is of finite-type
  have r6 : Fintype (Quotient (MulAction.orbitRel (Multiplicative (ZMod 2)) S)) := by
    have : DecidableRel (MulAction.orbitRel (Multiplicative (ZMod 2)) S).r := by
      rw [MulAction.orbitRel]; simp; simp [MulAction.orbit, DecidableRel]
      intro a b; apply Set.decidableSetOf
    apply Quotient.fintype
-- Apply Class Formula for this group action and prove $Nat.card S$ is even
  have r7 := MulAction.card_eq_sum_card_group_div_card_stabilizer (Multiplicative (ZMod 2)) S
  simp only [r5] at r7; simp at r7
  use Fintype.card (Quotient (MulAction.orbitRel (Multiplicative (ZMod 2)) ↑S))
  ring_nf; rw [← r7, Fintype.card_eq_nat_card]

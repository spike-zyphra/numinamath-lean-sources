import Mathlib
open Finset Nat FiniteField ZMod
open scoped Nat
namespace ZMod

-- Introduce Wilson's lemma to simplify the proof.
lemma wilsons_lemma_fixed (p : ℕ) (hp : Fact p.Prime): ((p - 1)! : ZMod p) = -1 := by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial, prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
          FiniteField.prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  symm
  refine prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_Ico, ← Nat.succ_sub hp, Nat.add_one_sub_one]
    constructor
    · apply Nat.pos_of_ne_zero
      intro h
      have h' : (a : ZMod p).val = ZMod.val (0 : ZMod p) := by
        rw [ZMod.val_zero, ← h]
      apply Units.ne_zero a
      apply val_injective p
      exact h'
    · exact ZMod.val_lt _
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact val_injective p h
  · intro b hb
    rw [Finset.mem_Ico, Nat.succ_le_iff, ← succ_sub hp, Nat.add_one_sub_one, pos_iff_ne_zero] at hb
    refine ⟨Units.mk0 b ?_, Finset.mem_univ _, ?_⟩
    · intro h; apply hb.1; apply_fun val at h
      simpa only [val_cast_of_lt hb.right, val_zero] using h
    · simp only [val_cast_of_lt hb.right, Units.val_mk0]
  · rintro a -; simp only [cast_id, natCast_val]

-- Prove that $(p - 1)$ in ZMod $p$ equals $p - 1$ in ZMod $p$ for a prime $p$.
lemma zmod_p_cast_pred (p : ℕ) (hp : Nat.Prime p) : (↑(p - 1) : ZMod p) = (↑p : ZMod p) - 1 := by
  have h_le : 1 ≤ p := Nat.le_of_lt (Nat.Prime.one_lt hp)
  rw [Nat.cast_sub h_le, Nat.cast_one]

/-Let $p$ be a prime number. Determine the remainder when $(p-1)!$ is divided by $p$. Show that this remainder is $p-1$.-/
theorem number_theory_6123456 (p : ℕ) (hp : Nat.Prime p):
  Nat.factorial (p - 1) ≡  p - 1 [MOD p] := by
  -- Convert to an equation in ZMod $p$.
  have h_wilson : ((p - 1)! : ZMod p) = -1 := by
    apply wilsons_lemma_fixed
    exact Fact.mk hp
  -- Prove that $-1 ≡ p - 1 (mod p)$ in ZMod $p$.
  have h_eq : (-1 : ZMod p) = (↑(p - 1) : ZMod p) := by
    rw [zmod_p_cast_pred p hp]
    norm_num
  have h_zmod : ((p - 1)! : ZMod p) = (p - 1 : ZMod p) := by
    rw [h_wilson, h_eq, zmod_p_cast_pred p hp]
  apply (ZMod.eq_iff_modEq_nat p).mp
  exact h_wilson.trans h_eq

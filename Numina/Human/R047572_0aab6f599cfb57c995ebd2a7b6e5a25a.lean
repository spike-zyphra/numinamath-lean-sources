import Mathlib

open Finset

/- Show that if \( p \) is an odd prime, then \( 2(p-3)! \equiv -1 \mod p \).-/
theorem number_theory_4787 {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    2 * ∏ i ∈ Ico 1 (p-2), i = (-1 : ZMod p) := by
  /- 原答案错误，以下为重写的正确证明。 -/
  /- Wilsons定理 -/
  have hwilsons := ZMod.wilsons_lemma p
  /- 奇素数大于等于3 -/
  have hpge : 3 ≤ p := by
    by_contra h
    have : 2 ≤ p := Nat.Prime.two_le <| Fact.out (p := p.Prime)
    interval_cases p
    have : ¬Odd 2 := by norm_num
    contradiction
  have hp1 : p - 3 + 1 = p - 2 := by
    rw [← Nat.sub_add_comm hpge]
    simp
  have hp2 : p - 1 = ((p - 3) + 1) + 1 := by
    simp
    rw [add_assoc, show 1+2=3 by norm_num]
    symm
    exact Nat.sub_add_cancel hpge
  /- (p-1)!=(p-1)(p-2)(p-3)! -/
  rw [hp2, Nat.factorial_succ, Nat.cast_mul, Nat.factorial_succ, Nat.cast_mul] at hwilsons
  rw [← Finset.prod_Ico_id_eq_factorial] at hwilsons
  /- p-1模p等于-1 -/
  have hp_sub_one : Nat.cast (p-3+1+1) = (-1 : ZMod p) := by
    rw [← hp2]
    suffices (Nat.cast (p-1) : ZMod p).val = (-1 : ZMod p).val by
      apply_fun (fun x => (x : ZMod p)) at this
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
      assumption
    calc
      _ = p-1 := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
        simp
        linarith
      _ = _ := by rw [ZMod.val_neg_of_ne_zero, ZMod.val_one]
  /- p-2模p等于-2 -/
  have hp_sub_two : Nat.cast (p-3+1) = (-2 : ZMod p) := by
    rw [hp1]
    suffices (Nat.cast (p-2) : ZMod p).val = (-2 : ZMod p).val by
      apply_fun (fun x => (x : ZMod p)) at  this
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at this
      assumption
    calc
      _ = p-2 := by
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
        simp
        linarith
      _ = _ := by
        have : NeZero (2 : ZMod p) := ⟨by
          intro h
          apply_fun (fun x => x.val) at h
          rw [show (2 : ZMod p) = Nat.cast 2 by norm_cast] at h
          rw [show (0 : ZMod p) = Nat.cast 0 by norm_cast] at h
          rw [ZMod.val_natCast, ZMod.val_natCast] at h
          rw [Nat.mod_eq_of_lt (show 2 < p by linarith)] at h
          rw [Nat.mod_eq_of_lt (show 0 < p by linarith)] at h
          norm_num at h⟩
        rw [ZMod.val_neg_of_ne_zero]
        suffices ZMod.val (2 : ZMod p) = 2 by rw [this]
        rw [show (2 : ZMod p) = Nat.cast 2 by norm_cast, ZMod.val_natCast]
        apply Nat.mod_eq_of_lt
        linarith
  /- (-1)(-2)模p等于2 -/
  rw [hp_sub_one, hp_sub_two] at hwilsons
  rw [← mul_assoc, show (-1 : ZMod p) * (-2) = 2 by ring] at hwilsons
  rw [hp1] at hwilsons
  exact hwilsons

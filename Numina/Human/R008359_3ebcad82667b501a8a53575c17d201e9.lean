import Mathlib

/-The units digit of the positive integer $a = 2003^{2004} - 2004^{2003}$ is.-/
theorem algebra_9395 : (2003 ^ 2004 - 2004 ^ 2003) % 10 = 7 := by
  rw [Nat.mod_eq_of_modEq, show 7=11-4 by norm_num]
-- Prove $2003^2004$ equals $11$ modulo $10$
  have m1 : 2003 ^ 2004 ≡ 11 [MOD 10] := by
-- Prove that $2003^2004$ equals $3 ^ 2004$ modulo $10$
    have r1 : 2003 ^ 2004 ≡ 3 ^ 2004 [MOD 10] := by
      apply Nat.ModEq.pow; rw [← ZMod.eq_iff_modEq_nat]
      reduce_mod_char
-- Prove that $3 ^ 2004$ equals $11$ modulo $10$
    nth_rw 2 [show 2004=4*501 by ring] at r1
    rw [pow_mul, show 3^4=81 by norm_num] at r1
    have r2 : 81 ^ 501 ≡ 1 ^ 501 [MOD 10] := by
      apply Nat.ModEq.pow; rw [← ZMod.eq_iff_modEq_nat]
      reduce_mod_char
-- Apply the transitivity of modulus and prove the goal
    apply Nat.ModEq.trans r1; apply Nat.ModEq.trans r2
    rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
--Prove $2004^2003$ equals $4$ modulo $10$
  have m2 : 2004 ^ 2003 ≡ 4 [MOD 10] := by
-- Prove that $2004^2003$ equals $4 ^ 2004$ modulo $10$
    have r1 : 2004 ^ 2003 ≡ 4 ^ 2003 [MOD 10] := by
      apply Nat.ModEq.pow; rw [← ZMod.eq_iff_modEq_nat]
      reduce_mod_char
-- Prove any odd power of $4$ equals $4$ modulo $10$ by induction
    have r2 : ∀ k, 4 ^ (2 * k + 1) ≡ 4 [MOD 10] := by
      intro k; induction k with
      | zero => simp; rfl
      | succ k ih =>
        rw [mul_add, mul_one, add_comm, ← add_assoc]
        nth_rw 2 [add_comm]; rw [pow_add, show 4^2=16 by norm_num]
        have : 4 ^ (2 * k + 1) * 16 ≡ 4 * 16 [MOD 10] := by
          apply Nat.ModEq.mul; assumption; rfl
        apply Nat.ModEq.trans this; simp
        rw [← ZMod.eq_iff_modEq_nat]; reduce_mod_char
-- Apply transitivity and r2 to prove the goal
    apply Nat.ModEq.trans r1; rw [show 2003=2*1001+1 by norm_num]
    apply r2
-- Apply Nat.ModEq.add_right_cancel and prove the final goal
  apply Nat.ModEq.add_right_cancel m2
  rw [Nat.sub_add_cancel, Nat.sub_add_cancel]; exact m1
  norm_num; linarith; norm_num
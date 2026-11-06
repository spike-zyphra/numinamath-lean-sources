import Mathlib

/-Prove the lemma that a square modulo $8$ is $0$, $1$ or $4$-/
lemma lm_8657 (x : ℤ): IsSquare x → x = (0: ZMod 8) ∨ x = (1: ZMod 8) ∨
x = (4: ZMod 8):= by
-- Rewrite assumptions
  intro h; rw [isSquare_iff_exists_sq] at h
  rcases h with ⟨a, ha⟩
  rw [show (0:ZMod 8)=(0:ℤ) by rfl]
  rw [show (1:ZMod 8)=(1:ℤ) by rfl, show (4:ZMod 8)=(4:ℤ) by rfl]
  rw [ZMod.intCast_eq_intCast_iff, ZMod.intCast_eq_intCast_iff]
  rw [ZMod.intCast_eq_intCast_iff]
-- Apply division with remainder on $a$
  have d8 := Int.emod_add_ediv a 8
-- Prove that the remainder is less than $8$
  have r8bpbd := @Int.emod_lt_of_pos a 8 (show (0:ℤ)<8 by norm_num)
  have r8lwbd := Int.emod_nonneg a (show (8:ℤ)≠0 by norm_num)
-- Split the goal to $8$ cases with respect to the remainder modulo $8$
  interval_cases (a % 8)
  · simp_all; left; rw [← d8, Int.modEq_zero_iff_dvd]
    use 8*(a/8)^2; ring
  · simp_all; right; left; rw [← d8]; ring_nf
    rw [show 1+a/8*16+(a/8)^2*64=1+8*((a/8*2)+(a/8)^2*8) by ring]
    exact Int.modEq_add_fac_self
  · simp_all; right; right; rw [← d8]; ring_nf
    rw [show 4+a/8*32+(a/8)^2*64=4+8*((a/8*4)+(a/8)^2*8) by ring]
    exact Int.modEq_add_fac_self
  · simp_all; right; left; rw [← d8]; ring_nf
    rw [show 9+a/8*48+(a/8)^2*64=1+8*(1+(a/8*6)+(a/8)^2*8) by ring]
    exact Int.modEq_add_fac_self
  · simp_all; left; rw [← d8, Int.modEq_zero_iff_dvd]
    use 2*(1+2*(a/8))^2; ring
  · simp_all; right; left; rw [← d8]; ring_nf
    rw [show 25+a/8*80+(a/8)^2*64=1+8*(3+(a/8*10)+(a/8)^2*8) by ring]
    exact Int.modEq_add_fac_self
  · simp_all; right; right; rw [← d8]; ring_nf
    rw [show 36+a/8*96+(a/8)^2*64=4+8*(4+(a/8*12)+(a/8)^2*8) by ring]
    exact Int.modEq_add_fac_self
  simp_all; right; left; rw [← d8]; ring_nf
  rw [show 49+a/8*112+(a/8)^2*64=1+8*(6+(a/8*14)+(a/8)^2*8) by ring]
  exact Int.modEq_add_fac_self

/-Let  $a$ ,  $b$ , and  $c$ be integers greater than zero. Show that the numbers   $$ 2a ^ 2 + b ^ 2 + 3 \,\,,  2b ^ 2 + c ^ 2 + 3\,\,,  2c ^ 2 + a ^ 2 + 3  $$     cannot be all perfect squares.-/
theorem number_theory_8657 (a b c : ℤ) (_ : 0 < a)(_ : 0 < b)(_ : 0 < c) :
¬ (IsSquare (2 * a ^ 2 + b ^ 2 + 3) ∧ IsSquare (2 * b ^ 2 + c ^ 2 + 3) ∧
IsSquare (2 * c ^ 2 + a ^ 2 + 3)) := by
-- Rewrite the goal and introduce more assumptions
  push_neg; intro sqab sqbc sqca
-- Apply the lemma lm to $a^2$, $b^2$ and $c^2$
  have ha := lm_8657 (a^2) (show IsSquare (a^2) by rw [isSquare_iff_exists_sq]; use a)
  have hb := lm_8657 (b^2) (show IsSquare (b^2) by rw [isSquare_iff_exists_sq]; use b)
  have hc := lm_8657 (c^2) (show IsSquare (c^2) by rw [isSquare_iff_exists_sq]; use c)
-- Apply the lemma lm to $2 * a ^ 2 + b ^ 2 + 3$, $2 * b ^ 2 + c ^ 2 + 3$ and $2 * c ^ 2 + a ^ 2 + 3$
  apply lm_8657 at sqab; apply lm_8657 at sqbc; apply lm_8657 at sqca
-- Simplify the type conversion
  push_cast at *
-- Split all possible cases and use "all_goals" command to find contradictions in each cases
  rcases ha with ha|ha|ha <;> rcases hb with hb|hb|hb <;>
  rcases hc with hc|hc|hc
  all_goals simp_all; contradiction

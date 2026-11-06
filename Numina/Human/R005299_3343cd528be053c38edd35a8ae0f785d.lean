import Mathlib

/-Existe-t-il des nombres rationnels positifs ou nuls $x, y$ et $z$ tels que:

$$
x^{5}+2 y^{5}+5 z^{5}=11
$$-/
theorem number_theory_607462 : ¬ ∃ x y z : ℚ, 0 < x ∧ 0 < y ∧ 0 < z ∧
x ^ 5 + 2 * y ^ 5 + 5 * z ^ 5 = 11 := by
-- According to the reference answer, we need the lemma that for any $n$, $n^5$ modulo $11$ can only be $0$, $1$ or $10$
  have lm : ∀ n, n ^ 5 % 11 = 0 ∨ n ^ 5 % 11 = 1 ∨ n ^ 5 % 11 = 10 := by
    intro n; have := Nat.mod_lt n (show 0<11 by simp)
    rw [Nat.pow_mod]; interval_cases n % 11; all_goals simp_all
-- Assume the contrary that there exists such numbers $x$, $y$ and $z$
  rintro ⟨x, y, z, xpos, ypos, zpos, heq⟩
-- Rewrite $x$, $y$ and $z$ into fractions
  rw [← Rat.num_div_den x, ← Rat.num_div_den y, ← Rat.num_div_den z] at heq
-- Rewrite the positivity assumptions
  rw [← Rat.num_div_den x, div_pos_iff_of_pos_right] at xpos; norm_cast at xpos
  rw [← Rat.num_div_den y, div_pos_iff_of_pos_right] at ypos; norm_cast at ypos
  rw [← Rat.num_div_den z, div_pos_iff_of_pos_right] at zpos; norm_cast at zpos
-- Clear the denominators on both sides of heq and norm_cast it to $ℕ$
  field_simp at heq; norm_cast at heq; push_cast at heq; ring_nf at heq
  simp [← mul_pow] at heq; apply_fun fun t => t.natAbs at heq
  rw [Int.natAbs_add_of_nonneg, Int.natAbs_add_of_nonneg] at heq; repeat rw [Int.natAbs_mul] at heq
  simp at heq; repeat rw [Int.natAbs_pow] at heq
  repeat rw [Int.natAbs_mul] at heq
  simp at heq
-- Rewrite heq to an existence form
  have dex : ∃ d : ℕ, ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 5 + b ^ 5 * 5 + c ^ 5 * 2 = d ^ 5 * 11 := by
    use y.den * x.den * z.den; use x.num.natAbs * y.den * z.den; use y.den * x.den * z.num.natAbs
    use y.num.natAbs * x.den * z.den; split_ands; any_goals positivity
    exact heq
-- Find the smallest $d$ satisfying $a ^ 5 + b ^ 5 * 5 + c ^ 5 * 2 = d ^ 5 * 11$
  have : DecidablePred fun n => ∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 5 + b ^ 5 * 5 + c ^ 5 * 2 = n ^ 5 * 11 := by apply Classical.decPred
  obtain ⟨a, b, c, apos, bpos, cpos, heq'⟩ := Nat.find_spec dex; have lediff := Nat.find_le_iff dex
  set d := Nat.find dex; have dpos : 0 < d := by by_contra!; simp at this; simp [this] at heq'; linarith
-- Prove that $a$, $b$ and $c$ have no common divisor since otherwise $d$ would not be the smallest
  have hgcd : (a.gcd b).gcd c = 1 := by
  -- Assume the contrary that the greatest common divisor of $a$, $b$ and $c$ is not $1$
  -- then we can take a prime factor $p$ of it, prove that $p$ divides $a$, $b$ and $c$
    by_contra! h; obtain ⟨p, ⟨ppr, pdvd⟩⟩ := Nat.exists_prime_and_dvd h
    have := ppr.two_le; rw [Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, and_assoc] at pdvd
    repeat rw [Nat.dvd_iff_mod_eq_zero] at pdvd
    rw [← Nat.mod_add_div a p, ← Nat.mod_add_div b p, ← Nat.mod_add_div c p] at heq'
    simp [pdvd.left, pdvd.right.left, pdvd.right.right] at heq'; repeat rw [mul_pow] at heq'
    rw [mul_assoc, ← Nat.mul_add, mul_assoc, ← Nat.mul_add] at heq'
  -- Prove that $p$ divides $d$
    have : p ∣ d := by
      by_cases hp : p ≠ 11
      · have : p.Coprime 11 := by rw [Nat.coprime_primes]; exact hp; exact ppr; norm_num
        rw [← Prime.dvd_pow_iff_dvd ppr.prime (show 5≠0 by simp), ← Nat.Coprime.dvd_mul_right this]
        rw [← heq']; apply dvd_trans (show p ∣ p ^ 5 by apply dvd_pow_self; simp); simp
      push_neg at hp; rw [← Prime.dvd_pow_iff_dvd ppr.prime (show 5≠0 by simp), hp]
      rw [hp] at heq'; use 11^3*((a / 11) ^ 5 + (b / 11) ^ 5 * 5 + (c / 11) ^ 5 * 2)
      rw [← Nat.mul_left_inj (show 11≠0 by simp), ← heq']; ring
    rw [Nat.dvd_iff_mod_eq_zero] at this; rw [← Nat.mod_add_div d p, this, zero_add, mul_pow] at heq'
    rw [mul_assoc, mul_left_cancel_iff_of_pos] at heq'; repeat rw [← Nat.dvd_iff_mod_eq_zero] at pdvd
  -- Prove some positivity results we need
    have adppos : 0 < a / p := by
      rw [Nat.div_pos_iff]; constructor; positivity; apply Nat.le_of_dvd
      exact apos; exact pdvd.left
    have bdppos : 0 < b / p := by
      rw [Nat.div_pos_iff]; constructor; positivity; apply Nat.le_of_dvd
      exact bpos; exact pdvd.right.left
    have cdppos : 0 < c / p := by
      rw [Nat.div_pos_iff]; constructor; positivity; apply Nat.le_of_dvd
      exact cpos; exact pdvd.right.right
  -- Specialize lediff at $d/p$ to show $d$ is less than $d/p$, which is a contradiction
    have := (lediff (d/p)).mpr (by use d/p; simp; use a/p; constructor; exact adppos; use b/p; constructor; exact bdppos; use c/p)
    convert this; simp; rw [Nat.div_lt_iff_lt_mul, Nat.lt_mul_iff_one_lt_right]; any_goals linarith
    positivity
-- Modulo $11$ on both sides of heq and simplify
  apply_fun fun t => t % 11 at heq'; simp [Nat.add_mod] at heq'; repeat rw [Nat.mod_mod] at heq'
  rw [Nat.mul_mod] at heq'; nth_rw 2 [Nat.mul_mod] at heq'
-- Apply lm to $a$, $b$ and $c$ and check all possibilities
  rcases lm a with am|am|am <;> rcases lm b with bm|bm|bm <;> rcases lm c with cm|cm|cm
  any_goals simp [am, bm, cm] at heq'
-- The only possibility is when $11$ divides $a$, $b$ and $c$, which contradicts to hgcd which says $a$, $b$ and $c$ have no common divisor
  replace am : 11 ∣ a := by
    rw [← Nat.dvd_iff_mod_eq_zero, Prime.dvd_pow_iff_dvd] at am; exact am
    rw [← Nat.prime_iff]; norm_num; simp
  replace bm : 11 ∣ b := by
    rw [← Nat.dvd_iff_mod_eq_zero, Prime.dvd_pow_iff_dvd] at bm; exact bm
    rw [← Nat.prime_iff]; norm_num; simp
  replace cm : 11 ∣ c := by
    rw [← Nat.dvd_iff_mod_eq_zero, Prime.dvd_pow_iff_dvd] at cm; exact cm
    rw [← Nat.prime_iff]; norm_num; simp
  suffices : 11 ∣ 1; contradiction
  rw [← hgcd, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff, and_assoc]; split_ands; any_goals assumption
  all_goals positivity
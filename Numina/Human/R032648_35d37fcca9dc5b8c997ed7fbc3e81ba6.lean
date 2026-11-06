import Mathlib

/-Find the smallest three-digit palindrome whose product with 101 is not a five-digit palindrome.-/
theorem number_theory_12741 :
IsLeast {n | n ≤ 999 ∧ 100 ≤ n ∧ Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧
Nat.digits 10 (101 * n) ≠ List.reverse (Nat.digits 10 (101 * n))} 505 := by
-- Rewrite goals and simplify
  rw [IsLeast, lowerBounds]; simp
-- Introduce assumptions
  intro m hm1 hm2 hm3 hm4
  have : ∃ a b c, Nat.digits 10 m = [a, b, c] := by
    rw [← List.length_eq_three, Nat.digits_len]
    simp; rw [Nat.log_eq_iff]; norm_num
    constructor; assumption; linarith
    constructor; norm_num; norm_num; linarith
  rcases this with ⟨a, b, c, hL⟩
-- Prove that $m$ modulo $10$ is $a$
  have mod1: m % 10 = a := by
    rw [← Nat.ofDigits_digits 10 m, Nat.ofDigits_mod_eq_head!]
    rw [hL]; norm_num; apply Nat.digits_lt_base; norm_num
    rw [hL]; norm_num
-- Prove that $m/10$ modulo $10$ is $b$
  have mod2 : (m / 10) % 10 = b := by
    rw [← Nat.ofDigits_digits 10 m, hL, Nat.ofDigits_div_eq_ofDigits_tail]
    norm_num; rw [Nat.ofDigits_mod_eq_head!]; norm_num
    apply Nat.digits_lt_base; norm_num
    rw [hL]; norm_num; norm_num
    rw [← hL]; intro l hl; apply Nat.digits_lt_base _ hl
    norm_num
-- Prove that $m/100$ modulo $10$ is $c$
  have mod3 : (m / 100) % 10 = c := by
    rw [show 100=10*10 by norm_num, ← Nat.div_div_eq_div_mul]
    rw [← Nat.ofDigits_digits 10 (m/10), Nat.ofDigits_div_eq_ofDigits_tail]
    have : Nat.digits 10 (m / 10) = [b, c] := by
      have := Nat.digits_eq_cons_digits_div (show 1<10 by norm_num) (show m≠0 by linarith)
      apply_fun (fun x => x.tail) at this
      simp [hL] at this; symm; assumption
    simp [this]; apply Nat.digits_lt_base; norm_num
    rw [this]; norm_num; norm_num
    intro l hl; apply Nat.digits_lt_base _ hl
    norm_num
-- Since $m$ is palindrome, it must be of the form $aba$
  simp [hL] at hm3; replace hm3 := hm3.left
  rw [← hm3] at hL mod3
-- If $a$ is less than $5$, prove that $101*n$ is palindrome, which contradicts to our assumption
  by_cases h' : a < 5
-- Prove the following inequality for later use
  have lm : 100 * m % 1000 + m % 1000 < 1000 := by
    nth_rw 1 [show 1000=100*10 by norm_num]
    rw [Nat.mul_mod_mul_left, mod1, Nat.mod_eq_of_lt]
    rw [← Nat.ofDigits_digits 10 m, hL, Nat.ofDigits_eq_sum_mapIdx]; simp
    have : b < 10 := by apply Nat.digits_lt_base; norm_num; rw [hL]; norm_num
    any_goals linarith
-- Prove that the digits of $101*m$ is of the form $ab(2a)ba$, the key lemma we will use here is Nat.digits_eq_cons_digits_div.
-- It reduces the digits of $101*m$ by one every time we apply it
  have : Nat.digits 10 (101 * m) = [a, b, 2*a, b ,a] := by
    rw [Nat.digits_eq_cons_digits_div, Nat.mul_mod]
    norm_num; constructor; assumption
    rw [Nat.digits_eq_cons_digits_div]
    nth_rw 1 [show 101=100+1 by norm_num]
    nth_rw 1 [add_mul, one_mul, Nat.add_div_of_dvd_right]
    rw [mul_comm, Nat.mul_div_assoc]; norm_num
    rw [Nat.add_mod, Nat.mul_mod_left]; norm_num
    constructor; assumption
    rw [Nat.div_div_eq_div_mul]; norm_num
    rw [Nat.digits_eq_cons_digits_div, Nat.div_div_eq_div_mul]; norm_num
    nth_rw 1 [show 101=100+1 by norm_num, add_mul, one_mul]
    rw [Nat.add_div_of_dvd_right, mul_comm, Nat.mul_div_assoc]; norm_num
    rw [Nat.add_mod, mod1]; norm_num
    rw [Nat.add_mod_of_add_mod_lt, Nat.mod_eq_of_lt, mod3]
    constructor; ring
    rw [show 101=100+1 by norm_num, add_mul, one_mul]
    rw [Nat.add_div]; split; linarith
    rw [show m/1000=0 by rw [Nat.div_eq_zero_iff]; omega]
    norm_num;
    rw [show 1000=100*10 by norm_num, Nat.mul_div_mul_left]
    have := Nat.digits_eq_cons_digits_div (show 1<10 by norm_num) (show m≠0 by linarith)
    apply_fun (fun x => x.tail) at this
    simp [hL] at this; symm; assumption
    norm_num; norm_num; linarith
    rw [Nat.mod_eq_of_lt, mod3]; linarith; linarith
    rfl; use m; norm_num
    intro h; rw [Nat.div_eq_zero_iff] at h; omega
    norm_num; use 10*m; ring; norm_num
    intro h; rw [Nat.div_eq_zero_iff] at h; omega
    norm_num; linarith
  push_neg at hm4; rw [this] at hm4; contradiction
-- Now we have $a$ greater or equal to $5$, we can write out the 10-adic expansion of $a$
-- and prove the final goal
  push_neg at h'; rw [← Nat.ofDigits_digits 10 m, hL]
  rw [Nat.ofDigits_eq_sum_mapIdx]; simp; linarith

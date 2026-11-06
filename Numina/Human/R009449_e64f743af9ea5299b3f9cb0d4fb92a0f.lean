import Mathlib

set_option maxHeartbeats 800000
/-Let $n>1$ be a given integer. Prove that infinitely many terms of the sequence $\left(a_{k}\right)_{k \geqslant 1}$, defined by  $$ a_{k}=\left\lfloor\frac{n^{k}}{k}\right\rfloor $$  are odd. (For a real number $x,\lfloor x\rfloor$ denotes the largest integer not exceeding $x$.) (Hong Kong)-/
theorem number_theory_24470 (n : ℕ) (ngt : 1 < n) (a : ℕ → ℕ)
(ha : ∀ k, a k = n ^ (k + 1) / (k + 1)) : {x : ℕ | x ∈ a '' Set.univ ∧ Odd x}.Infinite := by
-- For simplicity, denote the set in question by $S$
  set S := {x : ℕ | x ∈ a '' Set.univ ∧ Odd x} with hS
  replace ngt : 2 ≤ n := by linarith
-- Use induction to prove the following auxillary lemma for later use
  have aux : ∀ m, n ^ m ≤ n ^ (2 * m) - 2 * m := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      by_cases hm : m < 1
      · simp at hm; simp [hm]; zify; rw [Nat.cast_sub]; push_cast
        rw [← sub_nonneg, show (n:ℤ) ^ 2 - 2 - n = (n - 2) * (n + 1) by ring]
        simp; exact ngt; rw [pow_two]; suffices : 2 * 2 ≤ n * n; linarith
        exact Nat.mul_le_mul ngt ngt
      push_neg at hm; rw [Nat.le_sub_iff_add_le] at *
      apply Nat.mul_le_mul_left n at ih; rw [mul_add, ← pow_succ', ← pow_succ'] at ih
      have : n ^ (m + 1) + 2 * (m + 1) ≤ n ^ (m + 1) + n * (2 * m) := by
        simp; nth_rw 2 [mul_comm]; rw [mul_assoc]; simp
        suffices : m + 1 ≤ m * 2
        · apply le_trans this; apply mul_le_mul; rfl
          exact ngt; any_goals simp
        rw [mul_two]; simp; exact hm
      suffices : n ^ (2 * m + 1) ≤ n ^ (2 * (m + 1)); linarith
      apply Nat.pow_le_pow_right; any_goals linarith
      any_goals apply le_of_lt; apply Nat.lt_pow_self; linarith
-- Rewrite the goal by applying Set.infinite_iff_exists_gt, we will prove that given any $A$, there exists a number in $S$ larger than $A$
  rw [Set.infinite_iff_exists_gt]; intro A
-- Split the goal to two cases depending on the parity of $n$
  by_cases par : Odd n
  -- When $n$ is odd, define a new number $t$ to be $Nat.clog n (Nat.clog n (A + 1))$
  · simp [hS, ha]; let t := Nat.clog n (Nat.clog n (A + 1))
  -- Prove an inequality about $t$ by applying properties of $Nat.clog$
    have tmph1 : Nat.clog n (Nat.clog n (A + 1)) ≤ t := by simp [t]
    rw [← Nat.le_pow_iff_clog_le] at tmph1; specialize aux t
    replace tmph1 := le_trans tmph1 aux
    rw [← Nat.le_pow_iff_clog_le, ← Nat.pow_div, Nat.add_one_le_iff] at tmph1
  -- Prove that the number $n ^ n ^ (2 * t) / n ^ (2 * t)$ satisfies the desired properties
    use n ^ n ^ (2 * t) / n ^ (2 * t); split_ands
    · use n ^ (2 * t) - 1; rw [Nat.sub_add_cancel]
      apply Nat.one_le_pow; linarith
    · rw [Nat.pow_div]; apply Odd.pow; exact par
      apply le_of_lt; apply Nat.lt_pow_self; any_goals linarith
    exact tmph1; apply le_of_lt; apply Nat.lt_pow_self; any_goals linarith
-- When $n$ is even, rewrite $n$ as $2t$ for some number $t$
  rw [Nat.not_odd_iff_even] at par; rcases par with ⟨t, ht⟩
  rw [← two_mul] at ht;
  have tge : 1 ≤ t := by by_contra!; simp_all
-- Define a new number $m$ to be the maximum of $2$ and $Nat.clog 2 (Nat.clog n (A + 2))$
  let m := 2 ⊔ Nat.clog 2 (Nat.clog n (A + 2))
  have mge2 : 2 ≤ m := by simp [m]
-- Rewrite the following inequality of $m$ to an inequality on powers
  have mge : Nat.clog 2 (Nat.clog n (A + 2)) ≤ m := by simp [m]
  repeat rw [← Nat.le_pow_iff_clog_le] at mge
  have tmph1 : 2 ^ (2 ^ m - m) * t ^ 2 ^ m - 1 ≠ 1 := by
    intro h; simp at h; suffices : 1 < 2 ^ m - m
    · suffices : 2^1 * 1 < 2 ^ (2 ^ m - m) * t ^ 2 ^ m; linarith
      apply mul_lt_mul; rw [Nat.pow_lt_pow_iff_right]; exact this; any_goals simp
      apply Nat.one_le_pow; linarith
    rw [Nat.lt_sub_iff_add_lt, ← Nat.sub_lt_sub_iff_right (show 2 ≤ 1+m by linarith)]
    nth_rw 1 [show 2 = 1+1 by simp, ← Nat.sub_sub, Nat.add_sub_cancel_left]
    suffices : m - 1 < 2 ^ (m - 1)
    · apply lt_of_lt_of_le this; nth_rw 2 [show m = m-1+1 by rw [Nat.sub_add_cancel]; linarith]
      rw [pow_succ, mul_two, Nat.add_sub_assoc]; simp
      nth_rw 1 [show 2 = 2^1 by simp]; rw [Nat.pow_le_pow_iff_right, Nat.le_sub_iff_add_le]
      any_goals linarith
    apply Nat.lt_pow_self; simp
-- According to the reference answer, we can pick a prime divisor $p$ of $2 ^ (2 ^ m - m) * t ^ 2 ^ m - 1$
  obtain ⟨p, ⟨hp, pdvd⟩⟩ := Nat.exists_prime_and_dvd tmph1
-- Prove that $p$ is odd since it is a divisor of an odd number
  have podd : Odd p := by
    apply hp.odd_of_ne_two; intro h; rw [h] at pdvd
    suffices : ¬ 2 ∣ 2 ^ (2 ^ m - m) * t ^ 2 ^ m - 1; contradiction
    have : 2 ^ m - m = 2 ^ m - m - 1 + 1 := by
      rw [Nat.sub_add_cancel]; rw [← zero_add 1, Nat.add_one_le_iff]
      rw [Nat.lt_sub_iff_add_lt, zero_add]; apply Nat.lt_pow_self; simp
    rw [this, pow_succ', mul_assoc]; apply Nat.two_not_dvd_two_mul_sub_one
    positivity
-- Prove that $p$ is greater or equal to $3$
  have pge : 3 ≤ p := by
    by_contra!; interval_cases p; any_goals simp_all
    any_goals contradiction
-- Prove some facts which will be repeatedly used later, the first one is a simple inequality
  have tmph2 : m ≤ 2 ^ m * p := by
    nth_rw 1 [← mul_one m]; apply mul_le_mul; apply le_of_lt
    apply Nat.lt_pow_self; any_goals linarith
    simp
-- The second one is a division relation, we will first rewrite it to a congruence relation
  have tmph3 : 2 ^ m * p ∣ n ^ (2 ^ m * p) - 2 ^ m := by
    rw [← Nat.modEq_iff_dvd'] at *
    rw [← Nat.modEq_and_modEq_iff_modEq_mul]; constructor
    · rw [Nat.modEq_iff_dvd', ht, mul_pow]
      rw [show 2^m*p = m+(2^m*p-m) by rw [Nat.add_sub_cancel']; exact tmph2, pow_add]
      nth_rw 5 [← mul_one (2 ^ m)]; rw [mul_assoc, ← Nat.mul_sub]; simp
      suffices : 2 ^ m ≤ n ^ m
      · apply le_trans this; rw [Nat.pow_le_pow_iff_right]
        exact tmph2; linarith
      rw [Nat.pow_le_pow_iff_left]; any_goals linarith
  -- Apply various properties of Nat.ModEq to rewrite the goal and the hypothesis pdvd
    rw [Nat.ModEq.comm, pow_mul]; apply Nat.ModEq.mul_left (2 ^ m) at pdvd
    rw [mul_one, ← mul_assoc, ← pow_add, Nat.add_sub_cancel'] at pdvd
    rw [← mul_pow, ← ht, Nat.ModEq.comm] at pdvd; apply Nat.ModEq.pow p at pdvd
    apply Nat.ModEq.trans pdvd; rw [← Nat.pow_mul, Nat.pow_mul']
    apply Nat.ModEq.pow; suffices : 2 ^ (p - 1) ≡ 1 [MOD p]
    · apply Nat.ModEq.mul_left 2 at this
      rw [← pow_succ', mul_one, Nat.sub_add_cancel] at this
      exact this; linarith
  -- Apply Fermat-Euler totient theorem to finish the goal
    rw [show p-1 = p.totient by symm; exact Nat.totient_prime hp]
    apply Nat.ModEq.pow_totient; simp; exact podd
    apply le_of_lt; exact Nat.lt_two_pow_self
    rw [Nat.coprime_pow_left_iff]; simp; exact podd
    linarith; rw [show 1 = 1*1 by simp]; apply mul_le_mul
    any_goals apply Nat.one_le_pow; linarith
    any_goals simp
    suffices : 2 ^ m ≤ n ^ m
    · apply le_trans this; rw [Nat.pow_le_pow_iff_right]
      exact tmph2; linarith
    rw [Nat.pow_le_pow_iff_left]; any_goals linarith
-- According to the reference answer, prove that the number $(n ^ (2 ^ m * p) - 2 ^ m) / (2 ^ m * p)$ satisfies all the requirements of the final goal
  use (n ^ (2 ^ m * p) - 2 ^ m) / (2 ^ m * p); constructor
  · simp [S, ha]; constructor
  -- Show that $(n ^ (2 ^ m * p) - 2 ^ m) / (2 ^ m * p)$ is in $S$ by proving it equals $a (2 ^ m * p - 1)$
    · use 2 ^ m * p - 1; rw [Nat.sub_add_cancel]; apply Nat.div_eq_of_lt_le
      · rw [Nat.div_mul_cancel]; simp; exact tmph3
      rw [add_mul, one_mul, Nat.div_mul_cancel, ← Nat.sub_add_comm]
      rw [Nat.add_sub_assoc]; simp; linarith
      nth_rw 1 [← mul_one (2 ^ m)]; apply mul_le_mul; rfl; any_goals linarith
      simp; suffices : 2 ^ m ≤ n ^ m
      · apply le_trans this; rw [Nat.pow_le_pow_iff_right]
        exact tmph2; linarith
      rw [Nat.pow_le_pow_iff_left]; any_goals linarith
      exact tmph3
  -- Show that $(n ^ (2 ^ m * p) - 2 ^ m) /(2 ^ m * p)$ is odd by assuming the contrary, and then derive a contradiction on parities
    rw [← Nat.not_even_iff_odd]; intro h; rcases h with ⟨l, hl⟩
    rw [← two_mul, Nat.div_eq_iff_eq_mul_left, ht, mul_pow] at hl
    nth_rw 1 [show 2^m*p = m+(2^m*p-m) by rw [Nat.add_sub_cancel']; exact tmph2, pow_add] at hl
    rw [show 2*l*(2^m*p) = 2^m*(2*l*p) by ring, mul_assoc] at hl
    nth_rw 4 [← mul_one (2^m)] at hl; rw [← Nat.mul_sub, Nat.mul_left_cancel_iff] at hl
    replace hl : 2 ∣  2 ^ (2 ^ m * p - m) * t ^ (2 ^ m * p) - 1 := by rw [hl, mul_assoc]; simp
    suffices : ¬ 2 ∣ 2 ^ (2 ^ m * p - m) * t ^ (2 ^ m * p) - 1; contradiction
    have : 2 ^ m * p - m = 2 ^ m * p - m - 1 + 1 := by
      rw [Nat.sub_add_cancel]; rw [← zero_add 1, Nat.add_one_le_iff]
      rw [Nat.lt_sub_iff_add_lt, zero_add]; nth_rw 1 [← mul_one m]
      apply mul_lt_mul; apply Nat.lt_pow_self; any_goals simp
      linarith
    rw [this, pow_succ', mul_assoc]; apply Nat.two_not_dvd_two_mul_sub_one
    any_goals positivity
    exact tmph3
-- Prove that $(n ^ (2 ^ m * p) - 2 ^ m) / (2 ^ m * p)$ is larger than $A$
-- we will proceed by proving a sequence of three inequalities and finish the goal by linarith
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le, Nat.le_sub_iff_add_le]
  have : (A + 1) * (2 ^ m * p) + 2 ^ m ≤ (A + 2) * 2 ^ m * p := by
    rw [show (A + 2) * 2 ^ m * p = (A + 1) * (2 ^ m * p) + 2 ^ m * p by ring]
    simp; linarith
  have : (A + 2) * 2 ^ m * p ≤ n ^ (2 ^ m * 3) := by
    rw [show 2 ^ m * 3 = 2 ^ m + 2 ^ m + 2 ^ m by ring]
    repeat rw [pow_add]; apply mul_le_mul
    exact mge; apply le_of_lt; exact Nat.lt_pow_self ngt; any_goals simp
    suffices : p ∣ n ^ 2 ^ m - 2 ^ m
    · apply Nat.le_of_dvd at this; apply le_trans this
      exact Nat.sub_le (n ^ 2 ^ m) (2 ^ m); simp
      exact Nat.lt_pow_self ngt
    apply Nat.dvd_trans pdvd; rw [ht, mul_pow]
    nth_rw 3 [show 2 ^ m = m + (2 ^ m - m) by rw [Nat.add_sub_cancel']; apply le_of_lt; exact Nat.lt_two_pow_self]
    rw [pow_add]; nth_rw 6 [← mul_one (2 ^ m)]
    rw [mul_assoc, ← Nat.mul_sub]; simp
  have : n ^ (2 ^ m * 3) ≤ n ^ (2 ^ m * p) := by
    apply Nat.pow_le_pow_right; linarith; simp; exact pge
  any_goals linarith
  suffices : 2 ^ m ≤ n ^ m
  · apply le_trans this; rw [Nat.pow_le_pow_iff_right]
    exact tmph2; linarith
  rw [Nat.pow_le_pow_iff_left]; any_goals linarith

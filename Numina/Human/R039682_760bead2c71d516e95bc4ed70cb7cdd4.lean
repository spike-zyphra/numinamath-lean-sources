import Mathlib
set_option maxHeartbeats 0

/-20. (ARG) Prove that for each positive integer $n$, there exists a positive integer with the following properties: (i) It has exactly $n$ digits. (ii) None of the digits is 0 . (iii) It is divisible by the sum of its digits.-/
theorem other_24842 : ∀ n > 0, ∃ m, (Nat.digits 10 m).length = n ∧
(∀ i ∈ Nat.digits 10 m, i ≠ 0) ∧ (Nat.digits 10 m).sum ∣ m := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
-- Prove that $9$ divides $10^k-1$ for any number $k$
  have dvd9 : ∀ k, 9 ∣ 10 ^ k - 1 := by
    intro k; rw [← Nat.modEq_iff_dvd', Nat.ModEq.comm]
    rw [show 1 = 1^k by simp]; apply Nat.ModEq.pow; rfl
    apply Nat.one_le_pow'
-- Prove the following auxillary lemma for later use, it gives an alternative expression for numbers $rr...r$ with $r<10$
  have aux : ∀ k, ∀ r < 10, Nat.ofDigits 10 (List.replicate k r) = r * ((10 ^ k - 1) / 9) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      intro r hr; rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      by_cases h : r < 1
      · simp at h; simp_all
      push_neg at h; rw [← mul_assoc]; nth_rw 2 [mul_comm]
      nth_rw 1 [← mul_one r, mul_assoc, ← Nat.mul_add, Nat.mul_left_cancel_iff]
      rw [← Nat.mul_div_assoc, Nat.mul_sub, show 10*1 = 1+9*1 by simp]
      rw [← Nat.sub_sub, Nat.sub_mul_div, Nat.add_sub_cancel', pow_succ']
      rw [Nat.le_div_iff_mul_le, Nat.le_sub_iff_add_le, ← pow_succ']
      rw [show 1*9+1 = 10^1 by simp, Nat.pow_le_pow_iff_right]; any_goals simp
      rw [← pow_succ']; apply Nat.one_le_pow'
      rw [← pow_succ', Nat.le_sub_iff_add_le, show 1*9+1 = 10^1 by simp]
      rw [Nat.pow_le_pow_iff_right]; any_goals simp
      apply Nat.one_le_pow'; any_goals apply dvd9
      any_goals linarith
-- Prove the following auxillary division relation, we will compute values of padicValNat using padicValNat.pow_sub_pow
  have auxdvd : ∀ r, 3 ^ r ∣ (10 ^ 3 ^ r - 1) / 9 := by
    intro r; rw [padicValNat_dvd_iff]; right
    rw [show 9 = 3^2 by simp, show 1 = 1^3^r by simp]
    rw [padicValNat.div_pow, padicValNat.pow_sub_pow, padicValNat.pow]
    rw [show 10-1 = 3^2 by simp, padicValNat.pow]; any_goals simp
    use 1; any_goals norm_num
    rw [← Nat.modEq_iff_dvd', Nat.ModEq.comm]
    rw [show 1 = 1^3^r by simp]; apply Nat.ModEq.pow; rfl
    apply Nat.one_le_pow'
-- Introduce assumptions and write out the definition of Nat.log for later use
  intro n npos; have lgp : Nat.log 3 n = Nat.log 3 n := rfl
  rw [Nat.log_eq_iff, pow_succ'] at lgp
-- We first prove the case when $n$ is a power of $3$ by induction
  by_cases hn : ∃ r, n = 3 ^ r
  -- In this case, we show that the number $11...1$ with $3^r$ digits satisfies all the required properties
  · rcases hn with ⟨r, hr⟩; rw [hr]
    use (Nat.ofDigits 10 (List.replicate (3^r) 1)); split_ands
    any_goals rw [Nat.digits_ofDigits]; any_goals simp
  -- Prove that $3^r$ divides $11...1$ by applying lemma aux and auxdvd
    rw [aux, one_mul]; exact auxdvd r; simp
-- If $n$ is not a power of $3$, split the goal to two cases when $n$ is larger than $2*3^(Nat.log 3 n)$ or not
  push_neg at hn
  replace npos : 2 ≤ n := by
    by_contra!; replace this : n = 1 := by linarith
    specialize hn 0; simp at hn; contradiction
-- Prove the following auxillary inequality which will be repeatedly used later
  have tmph : 1 ≤ n - 3 ^ Nat.log 3 n := by
    rw [Nat.le_sub_iff_add_le', Nat.add_one_le_iff, lt_iff_le_and_ne]; constructor
    · apply Nat.pow_log_le_self; linarith
    symm; apply hn; apply Nat.pow_log_le_self; linarith
  rcases le_or_lt n (2 * 3 ^ (Nat.log 3 n)) with h|h
  -- If $n$ is less or equal to $2*3^(Nat.log 3 n)$, then according to the reference, we prove that $Nat.ofDigits 10 (8 :: List.replicate (n - 3 ^ (Nat.log 3 n) - 1) 7 ++ List.replicate (2 * 3 ^ (Nat.log 3 n) - n) 9 ++ [1] ++ List.replicate (n - 3 ^ (Nat.log 3 n) - 1) 2)$ satisfies all the requirements of the goal
  · use Nat.ofDigits 10 (8 :: List.replicate (n - 3 ^ (Nat.log 3 n) - 1) 7 ++ List.replicate (2 * 3 ^ (Nat.log 3 n) - n) 9 ++ [1] ++ List.replicate (n - 3 ^ (Nat.log 3 n) - 1) 2)
  -- Split the goal to two cases when $n - 3 ^ (Nat.log 3 n) - 1 = 0$ or not
    by_cases h' : n - 3 ^ (Nat.log 3 n) - 1 = 0
    -- Simplify the goal using h'
    · rw [Nat.digits_ofDigits]; simp
      simp [h']; replace h' : n = 3 ^ (Nat.log 3 n) + 1 := by
        rw [Nat.sub_sub, Nat.sub_eq_zero_iff_le] at h'
        rw [Nat.le_sub_iff_add_le] at tmph; linarith
        apply Nat.pow_log_le_self; linarith
      split_ands
      -- Prove the number in question has $n$ digits
      · zify; rw [Nat.cast_sub]; nth_rw 2 3 [h']
        push_cast; ring; exact h
      -- Prove all the digits of the number in question is nonzero
      · intro x hx; rcases hx with _|_; any_goals linarith
    -- Prove the sum of the digits divides the number in question, we proceed by first simplifying the divisor
      nth_rw 2 [h']; rw [show 8+((2*3^Nat.log 3 n-(3^Nat.log 3 n+1))*9+1) = 9*3^Nat.log 3 n by zify; rw [Nat.cast_sub]; push_cast; ring; rw [← h']; exact h]
    -- Simplify the dividend by applying properties of Nat.ofDigits
      rw [Nat.ofDigits_cons, Nat.ofDigits_append, aux]; simp
      rw [Nat.mul_div_cancel', mul_add, Nat.mul_sub, mul_one, ← pow_succ']
      rw [← add_assoc, ← Nat.add_sub_assoc]
      have : 2 * 3 ^ Nat.log 3 n - n + 1 = 3 ^ Nat.log 3 n := by
        zify; rw [Nat.cast_sub]; nth_rw 2 [h']
        push_cast; ring; exact h
      rw [this]; have : 8 + 10 ^ 3 ^ Nat.log 3 n - 10 + 10 ^ 3 ^ Nat.log 3 n = 2 * (10 ^ 3 ^ Nat.log 3 n - 1) := by
        zify; repeat rw [Nat.cast_sub]
        push_cast; ring; apply Nat.one_le_pow'
        nth_rw 1 [← zero_add 10, show 10 = 10^1 by simp]; apply add_le_add; simp
        rw [Nat.pow_le_pow_iff_right]; apply Nat.one_le_pow'; simp
    -- Apply the lemmas auxdvd and dvd9 to finish the goal
      rw [this]; suffices : 9 * 3 ^ Nat.log 3 n ∣ 10 ^ 3 ^ Nat.log 3 n - 1
      · apply Nat.dvd_trans this; simp
      rw [← Nat.dvd_div_iff_mul_dvd]; apply auxdvd
      any_goals apply dvd9
      nth_rw 1 [show 10 = 10^1 by simp]; rw [Nat.pow_le_pow_iff_right]; any_goals simp
      intro x hx; rcases hx with _|_|_|_; any_goals linarith
      rw [h']; simp
  -- Now we can assume that $n - 3 ^ (Nat.log 3 n) - 1$ is not $0$, then apply Nat.digits_ofDigits and simplify the goal
    push_neg at h'; rw [Nat.digits_ofDigits]; simp; split_ands
    -- Prove the number in question has $n$ digits
    · zify; repeat rw [Nat.cast_sub]
      push_cast; ring; exact h
      apply Nat.pow_log_le_self; linarith
      rw [Nat.le_sub_iff_add_le', Nat.add_one_le_iff, lt_iff_le_and_ne]; constructor
      · apply Nat.pow_log_le_self; linarith
      symm; apply hn; apply Nat.pow_log_le_self; linarith
    -- Prove all the digits of the number in question is nonzero
    · intro x hx; rcases hx with _|_|_|_; any_goals linarith
  -- Prove the sum of the digits divides the number in question, we proceed by first simplifying the divisor
    have tmph1 : 8 + ((n - 3 ^ Nat.log 3 n - 1) * 7 + ((2 * 3 ^ Nat.log 3 n - n) * 9 + (1 + (n - 3 ^ Nat.log 3 n - 1) * 2))) =
    9 * 3 ^ Nat.log 3 n := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; exact h; apply Nat.pow_log_le_self; linarith
      exact tmph
  -- Prove the following identity by applying lemma aux, which simplifies the dividend
    have tmph2 : Nat.ofDigits 10 (8 :: (List.replicate (n - 3 ^ Nat.log 3 n - 1) 7 ++ (List.replicate (2 * 3 ^ Nat.log 3 n - n) 9 ++ 1 :: List.replicate (n - 3 ^ Nat.log 3 n - 1) 2))) =
    (10 ^ 3 ^ (Nat.log 3 n) - 1) * Nat.ofDigits 10 (List.replicate (n - 3 ^ Nat.log 3 n) 2) := by
      rw [Nat.ofDigits_cons]; repeat rw [Nat.ofDigits_append]
      rw [Nat.ofDigits_cons]; simp; repeat rw [aux]
      qify; repeat rw [Nat.cast_sub]
      push_cast; repeat rw [Int.cast_div]
      push_cast; field_simp; any_goals simp
      any_goals apply Nat.one_le_pow'
      ring_nf; repeat rw [← pow_add]
      rw [add_sub, ← sub_eq_add_neg]
      have tmph2 : n - 3 ^ Nat.log 3 n - 1 + (3 ^ Nat.log 3 n * 2 - n) = 3 ^ Nat.log 3 n - 1 := by
        zify; repeat rw [Nat.cast_sub]
        push_cast; ring; apply Nat.one_le_pow'; rw [mul_comm]
        exact h; apply Nat.pow_log_le_self; linarith; exact tmph
      rw [tmph2, show (20:ℚ) = 10*2 by norm_num]
      repeat rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel]
      have tmph3 : (n - 3 ^ Nat.log 3 n - 1) * 2 + (3 ^ Nat.log 3 n * 2 - n) = n - 2 := by
        zify; repeat rw [Nat.cast_sub]
        push_cast; ring; exact npos
        rw [mul_comm]; exact h; apply Nat.pow_log_le_self
        linarith; exact tmph
      rw [tmph3, show (200:ℚ) = 10^2*2 by norm_num, ← mul_assoc, ← pow_add]
      rw [Nat.sub_add_cancel, Nat.sub_add_cancel]; ring
      apply Nat.pow_log_le_self; any_goals linarith
      any_goals rw [show (9:ℤ) = (9:ℕ) by rfl]; norm_cast; rw [Int.subNatNat_eq_coe, ← Nat.cast_sub]; norm_cast
      any_goals apply dvd9
      any_goals apply Nat.one_le_pow'
  -- After simplifying, we apply the lemmas auxdvd and dvd9 to finish the goal
    rw [tmph1, tmph2]; suffices : 9 * 3 ^ Nat.log 3 n ∣ (10 ^ 3 ^ Nat.log 3 n - 1)
    · apply Nat.dvd_trans this; simp
    rw [← Nat.dvd_div_iff_mul_dvd]; apply auxdvd; apply dvd9; any_goals simp
    intro x hx; rcases hx with _|_|_|_; any_goals linarith
    rw [List.getLast_cons, List.getLast_replicate]; simp
    intro h''; rw [List.replicate_eq_nil_iff] at h''; contradiction
-- If $n$ is greater than $2*3^Nat.log 3 n$, then according to the reference, we prove that $Nat.ofDigits 10 (8 :: List.replicate (n - 2 * 3 ^ (Nat.log 3 n) - 1) 7 ++ List.replicate (4 * 3 ^ (Nat.log 3 n) - n) 9 ++ [1] ++ List.replicate (n - 2 * 3 ^ (Nat.log 3 n) - 1) 2)$ satisfies all the requirements of the goal
  use Nat.ofDigits 10 (8 :: List.replicate (n - 2 * 3 ^ (Nat.log 3 n) - 1) 7 ++ List.replicate (4 * 3 ^ (Nat.log 3 n) - n) 9 ++ [1] ++ List.replicate (n - 2 * 3 ^ (Nat.log 3 n) - 1) 2)
-- Split the goal to two cases when $n - 3 ^ (Nat.log 3 n) - 1 = 0$ or not
  by_cases h' : n - 2 * 3 ^ (Nat.log 3 n) - 1 = 0
  · rw [Nat.digits_ofDigits]; simp
  -- When $n - 2 * 3 ^ (Nat.log 3 n) - 1 = 0$, we first use this assumption to simplify the goal
    simp [h']; replace h' : n = 2 * 3 ^ (Nat.log 3 n) + 1 := by
      rw [Nat.sub_sub, Nat.sub_eq_zero_iff_le] at h'
      rw [Nat.le_sub_iff_add_le] at tmph; linarith
      apply Nat.pow_log_le_self; linarith
    split_ands
    -- Prove the number in question has $n$ digits
    · zify; rw [Nat.cast_sub]; nth_rw 2 3 [h']
      push_cast; ring; linarith
    -- Prove all the digits of the number in question is nonzero
    · intro x hx; rcases hx with _|_; any_goals linarith
  -- Prove the sum of the digits divides the number in question, we proceed by first simplifying the divisor
    nth_rw 2 [h']; rw [show 8+((4*3^Nat.log 3 n-(2*3^Nat.log 3 n+1))*9+1) = 18*3^Nat.log 3 n by zify; rw [Nat.cast_sub]; push_cast; ring; rw [← h']; linarith]
  -- Simplify the dividend by applying properties of Nat.ofDigits
    rw [Nat.ofDigits_cons, Nat.ofDigits_append, aux]; simp
    rw [Nat.mul_div_cancel', mul_add, Nat.mul_sub, mul_one, ← pow_succ']
    rw [← add_assoc, ← Nat.add_sub_assoc]
    have : 4 * 3 ^ Nat.log 3 n - n + 1 = 2 * 3 ^ Nat.log 3 n := by
      zify; rw [Nat.cast_sub]; nth_rw 2 [h']
      push_cast; ring; linarith
    rw [this]; have : 8 + 10 ^ (2 * 3 ^ Nat.log 3 n) - 10 + 10 ^ (2 * 3 ^ Nat.log 3 n) = 2 * (10 ^ (2 * 3 ^ Nat.log 3 n) - 1) := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; apply Nat.one_le_pow'
      nth_rw 1 [← zero_add 10, show 10 = 10^1 by simp]; apply add_le_add; simp
      rw [Nat.pow_le_pow_iff_right]; rw [show 1 = 1*1 by simp]; apply mul_le_mul
      simp; apply Nat.one_le_pow'; any_goals simp
  -- Apply the lemmas auxdvd and dvd9 to finish the goal
    rw [this, show 18 = 2*9 by simp, mul_assoc, Nat.mul_dvd_mul_iff_left]
    rw [pow_mul', show 1 = 1^2 by simp, Nat.pow_two_sub_pow_two]
    suffices : 9 * 3 ^ Nat.log 3 n ∣ 10 ^ 3 ^ Nat.log 3 n - 1
    · apply Nat.dvd_trans this; simp
    rw [← Nat.dvd_div_iff_mul_dvd]; apply auxdvd
    any_goals apply dvd9
    any_goals simp
    nth_rw 1 [show 10 = 10^1 by simp]; rw [Nat.pow_le_pow_iff_right]; any_goals simp
    intro x hx; rcases hx with _|_|_|_; any_goals linarith
    rw [h']; simp
-- Now we can assume that $n - 2 * 3 ^ (Nat.log 3 n) - 1$ is not $0$, then apply Nat.digits_ofDigits and simplify the goal
  push_neg at h'; rw [Nat.digits_ofDigits]; simp; split_ands
  -- Prove the number in question has $n$ digits
  · zify; repeat rw [Nat.cast_sub]
    push_cast; ring; any_goals linarith
    exact Nat.le_sub_of_add_le' h
  -- Prove all the digits of the number in question is nonzero
  · intro x hx; rcases hx with _|_|_|_; any_goals linarith
  -- Prove the sum of the digits divides the number in question, we proceed by first simplifying the divisor
  have tmph1 : 8 + ((n - 2 * 3 ^ Nat.log 3 n - 1) * 7 + ((4 * 3 ^ Nat.log 3 n - n) * 9 + (1 + (n - 2 * 3 ^ Nat.log 3 n - 1) * 2))) =
  18 * 3 ^ Nat.log 3 n := by
    zify; repeat rw [Nat.cast_sub]
    push_cast; ring; any_goals linarith
    exact Nat.le_sub_of_add_le' h
  -- Prove the following identity by applying lemma aux, which simplifies the dividend
  have tmph2 : Nat.ofDigits 10 (8 :: (List.replicate (n - 2 * 3 ^ Nat.log 3 n - 1) 7 ++ (List.replicate (4 * 3 ^ Nat.log 3 n - n) 9 ++ 1 :: List.replicate (n - 2 * 3 ^ Nat.log 3 n - 1) 2))) =
  (10 ^ (2 * 3 ^ Nat.log 3 n) - 1) * Nat.ofDigits 10 (List.replicate (n - 2 * 3 ^ Nat.log 3 n) 2) := by
    rw [Nat.ofDigits_cons]; repeat rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_cons]; simp; repeat rw [aux]
    qify; repeat rw [Nat.cast_sub]
    push_cast; repeat rw [Int.cast_div]
    push_cast; field_simp; any_goals simp
    any_goals apply Nat.one_le_pow'
    ring_nf; repeat rw [← pow_add]
    rw [add_sub, ← sub_eq_add_neg]
    have tmph2 : n - 3 ^ Nat.log 3 n * 2 - 1 + (3 ^ Nat.log 3 n * 4 - n) = 3 ^ Nat.log 3 n * 2 - 1 := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; rw [show 1 = 1*1 by simp]; apply mul_le_mul
      apply Nat.one_le_pow'; any_goals simp
      any_goals linarith
      rw [mul_comm]; exact Nat.le_sub_of_add_le' h
    rw [tmph2, show (20:ℚ) = 10*2 by norm_num]
    repeat rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel]
    have tmph3 : (n - 3 ^ Nat.log 3 n * 2 - 1) * 2 + (3 ^ Nat.log 3 n * 4 - n) = n - 2 := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; exact npos
      any_goals linarith
      rw [mul_comm]; exact Nat.le_sub_of_add_le' h
    rw [tmph3, show (200:ℚ) = 10^2*2 by norm_num, ← mul_assoc, ← pow_add]
    rw [Nat.sub_add_cancel, Nat.sub_add_cancel]; ring
    any_goals linarith
    rw [mul_comm]; exact Nat.le_sub_of_add_le' h
    any_goals rw [show (9:ℤ) = (9:ℕ) by rfl]; norm_cast; rw [Int.subNatNat_eq_coe, ← Nat.cast_sub]; norm_cast
    any_goals apply dvd9
    any_goals apply Nat.one_le_pow'
-- After simplifying, we apply the lemmas auxdvd and dvd9 to finish the goal
  rw [tmph1, tmph2, show 18 = 2*9 by simp, mul_assoc]
  nth_rw 3 [mul_comm]; apply Nat.mul_dvd_mul
  · rw [aux]; any_goals simp
  rw [pow_mul', show 1 = 1^2 by simp, Nat.pow_two_sub_pow_two]
  suffices :  9 * 3 ^ Nat.log 3 n ∣ 10 ^ 3 ^ Nat.log 3 n - 1
  · apply Nat.dvd_trans this; simp
  rw [← Nat.dvd_div_iff_mul_dvd]; apply auxdvd; apply dvd9; any_goals simp
  intro x hx; rcases hx with _|_|_|_; any_goals linarith
  rw [List.getLast_cons, List.getLast_replicate]; any_goals simp
  intro h''
  apply h' h''
  right; linarith

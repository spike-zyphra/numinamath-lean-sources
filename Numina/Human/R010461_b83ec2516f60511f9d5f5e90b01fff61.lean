import Mathlib

open Real

/- Let $a = \frac{\pi}{2008}$. Find the smallest positive integer $n$ such that
$$2\left[\cos(a) \sin(a) + \cos(4a)\sin(2a) + \cos(9a)\sin(3a) + \cdots + \cos(n^2 a) \sin(na) \right]$$
is an integer. -/
theorem algebra_94020 {a : ℝ} (ha : a = π / 2008) :
    IsLeast {n : ℕ | 0 < n ∧ ∃ k : ℤ, 2 * ∑ i ∈ Finset.Icc 1 n, cos (i ^ 2 * a) * sin (i * a) = k} 251 := by
  -- using the identity 2 * sin x * cos y = sin (x - y) + sin (x + y), rewrite the term 2 * cos (k ^ 2 * a) * sin (k * a) as a difference of two sin functions
  have h_trig : ∀ k : ℕ, 2 * cos (k ^ 2 * a) * sin (k * a) = sin (k * (k + 1) * a) - sin ((k - 1) * k * a) := by
    intro k
    rw [mul_assoc, mul_comm (cos _), ←mul_assoc]
    rw [two_mul_sin_mul_cos, add_comm, sub_eq_add_neg (sin _), ← sin_neg]
    congr <;> ring
  -- show that the sum is equal to sin (n * (n + 1) * a) for all n > 0
  -- to simplify the proof, replace n with n + 1 in the statement to capture the fact that n > 0
  have heq : ∀ n : ℕ, 2 * ∑ i ∈ Finset.Icc 1 (n + 1), cos (i ^ 2 * a) * sin (i * a) = sin ((n + 1) * (n + 2) * a) := by
    -- proof by induction
    intro n; induction n with
    | zero => simp [sin_two_mul]; ac_nf
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ n + 1 + 1 by simp), mul_add, ih]
      -- use the identity proved at the beginning of the proof to simplify the goal
      rw [← mul_assoc 2, h_trig]
      rw [add_sub_left_comm]
      push_cast; ac_nf; norm_num
      rw [show (n : ℝ) + 2 - 1 = n + 1 by linarith, mul_comm ((n : ℝ) + 1), sub_self, add_zero, mul_comm ((n : ℝ) + 3)]
  -- unfold the definition of IsLeast
  simp [IsLeast, mem_lowerBounds]
  -- we need to prove 2 cases: n = 251 yields an integer result and for any n which yields an integer result n >= 251
  split_ands
  · use -1
    rw [show 251 = 250 + 1 by norm_num, heq, ha]
    norm_num
    rw [mul_div_left_comm, show (63252 : ℝ) / 2008 = 2 * 16 - 1 / 2 by norm_num]
    rw [mul_sub, show π * (2 * 16) - π * (1 / 2) = (16 : ℤ) * (2 * π) - π / 2 by push_cast; linarith]
    rw [sin_int_mul_two_pi_sub, sin_pi_div_two]
  · intro n hn k
    rw [show n = (n - 1) + 1 by omega, heq, show n - 1 + 1 = n by omega]
    push_cast [hn]
    rw [show n - (1 : ℝ) + 1 = n by linarith, show n - (1 : ℝ) + 2 = n + 1 by linarith]
    -- If sin(x) is integer then x = n * π / 2 for some integer n
    -- This well-known fact is missing in Mathlib but it is not difficult to prove
    have isInt_sin : ∀ x (k : ℤ), sin x = k → ∃ n : ℤ, x = n * π / 2 := by
      intro x k hsin
      suffices k = 0 ∨ k = 1 ∨ k = -1 from by
        rcases this with h | h | h <;> rw [h] at hsin
        · simp [sin_eq_zero_iff] at hsin
          rcases hsin with ⟨n, h⟩
          use 2 * n
          push_cast; linarith
        · simp [sin_eq_one_iff] at hsin
          rcases hsin with ⟨n, h⟩
          use 4 * n + 1
          push_cast; linarith
        · simp [sin_eq_neg_one_iff] at hsin
          rcases hsin with ⟨n, h⟩
          use 4 * n - 1
          push_cast; linarith
      rw [← Int.abs_le_one_iff]
      rify
      rw [← hsin]
      exact abs_sin_le_one x
    intro h1; apply isInt_sin at h1; rw [ha] at h1
    rcases h1 with ⟨k, hk⟩
    -- show that 251 (a prime number) divides n * (n + 1)
    have hnk : n * (n + 1) = 251 * (4 * k) := by
      rify
      apply mul_right_cancel₀ (show π / 2008 ≠ 0 by norm_num; exact pi_ne_zero)
      rw [hk]; ring
    -- we have two cases: 251 divides n or 251 divides n + 1
    have hn_div : 251 ∣ n ∨ 251 ∣ n + 1 := by
      apply (Nat.Prime.dvd_mul (by norm_num)).mp
      zify
      use 4 * k
    cases hn_div with
    | inl h => exact Nat.le_of_dvd hn h
    | inr h =>
      -- if 251 divides n + 1 then the minimal value of n is 250
      apply Nat.le_of_dvd (Nat.add_pos_left hn 1) at h
      rw [le_iff_eq_or_lt] at h
      cases h with
      | inl h =>
        -- if n = 250 then 250 * 251 = 251 * (4 * k) is impossible (4 does not divide the left hand side)
        have n_eq : n = 250 := by omega
        contrapose! hnk
        rw [n_eq]
        omega
      | inr h => omega
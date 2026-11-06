import Mathlib

/-On Monday, Jessica told two friends a secret. On Tuesday, each of those friends told the secret to two other friends. Each time a student heard the secret, he or she told the secret to two other friends the following day. On what day of the week will 1023 students know the secret?-/
theorem algebra_13400 {secret_known : ℕ → ℕ} (h : ∀ n, secret_known n = ∑ i ∈ Finset.range (n + 1), 2 ^ i) :
secret_known m = 1023 → m % 7 = 2 := by
-- introduce the assumption
  intro h'
-- Write out a closed formula for the number of people who know the secret on n-th day by induction
  have : ∀ n, secret_known n = 2 ^ (n + 1) - 1 := by
    intro n; induction n with
    | zero => simp [h]
    | succ n ih =>
      rw [h, Finset.sum_range_succ, ← h, ih, ← Nat.sub_add_comm]
      ring_nf; apply Nat.one_le_pow; norm_num
-- Apply the formula and solve for $m$, then prove the final goal
  rw [this] at h'; apply Nat.eq_add_of_sub_eq at h'
  rw [show 1023+1=2^10 by norm_num] at h'; apply Nat.pow_right_injective at h'
  simp at h'; rw [h']; norm_num
  apply Nat.one_le_pow; norm_num
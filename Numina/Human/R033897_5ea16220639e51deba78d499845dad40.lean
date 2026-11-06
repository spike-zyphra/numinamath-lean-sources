import Mathlib

theorem algebra_203168 {n : ℕ} (N : ℚ) (heq : √n + √(n + 524) = N) : N = 262 := by
  have : (524 : ℝ) = √(n + 524) ^ 2 - √n ^ 2 := by
    repeat rw [Real.sq_sqrt]
    ring; all_goals positivity
  obtain ⟨k, hk⟩ : IsSquare n := by
    rw [← Rat.isSquare_natCast_iff]
    use 1 / 2 * (N - 524 / N); rw [← pow_two]
    rify; rw [this, sq_sub_sq, add_comm, heq, mul_div_cancel_left₀]
    rw [← heq]; ring_nf; rw [Real.sq_sqrt]; positivity
    rw [← heq]; positivity
  obtain ⟨m, hm⟩ : IsSquare (n + 524) := by
    rw [← Rat.isSquare_natCast_iff]
    push_cast; use 1 / 2 * (N + 524 / N); rw [← pow_two]
    rify; nth_rw 3 [this]; rw [sq_sub_sq]; nth_rw 3 [add_comm]
    rw [heq, mul_div_cancel_left₀]
    rw [← heq]; ring_nf; rw [Real.sq_sqrt]; positivity
    rw [← heq]; positivity
  rw [← pow_two] at hk hm; norm_cast at heq
  rw [hm, hk] at heq; push_cast at heq; repeat rw [Real.sqrt_sq] at heq
  norm_cast at heq; rw [hk] at hm
  apply Nat.eq_sub_of_add_eq' at hm; rw [Nat.sq_sub_sq] at hm
  have : m + k ∈ Nat.divisors 524 := by simp; use m - k
  simp [show Nat.divisors 524 = {1, 2, 4, 131, 262, 524} by decide] at this
  apply Nat.div_eq_of_eq_mul_right at hm
  rcases this with h|h|h|h|h|h
  any_goals simp [h] at hm; omega
  rw [← heq, add_comm, h]; simp
  omega; all_goals positivity
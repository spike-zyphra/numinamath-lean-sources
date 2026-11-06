import Mathlib

theorem algebra_13820 {w t : ℕ} (ht : w = 2 * t) :
    w * t - (w + 4) * (t - 2) = (8 : ℤ) := by
  rw [ht]
  cases t with
  | zero =>
    all_goals
      norm_num
  | succ t =>
    cases t with
    | zero =>
      all_goals
        norm_num
    | succ t =>
      simp [Nat.mul_sub_left_distrib, Nat.mul_add, mul_comm, Nat.sub_mul, Nat.add_mul, Nat.mul_assoc]
      <;> ring_nf <;> omega
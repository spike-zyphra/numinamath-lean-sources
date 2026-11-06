import Mathlib

/-For how many integer values of $a$ does the equation $$x^2 + ax + 8a = 0$$ have integer solutions for $x$?-/
theorem algebra_11745 : {a | ∃ x : ℤ, x ^ 2 + a * x + 8 * a = 0}.ncard = 8 := by
-- Find out explicitly the set of integers $a$ such that the given equation has integer solutions
  have SLa : {a | ∃ x : ℤ, x ^ 2 + a * x + 8 * a = 0} = {-49,-18,-4,0,32,36,50,81} := by
    ext a; simp; constructor
-- Rewrite the equation and prove that $x+8$ is a divisor of $64$
    · rintro ⟨x, h⟩; apply_fun (fun t => - t + 64) at h; rw [neg_zero, zero_add] at h
      rw [show -(x ^ 2 + a * x + 8 * a) + 64 = (x + 8) * (8 - x - a) by ring] at h
      have : (x+8).natAbs ∈ Nat.divisors 64 := by
        rw [Nat.mem_divisors]; norm_num
        use (8 - x - a).natAbs; rw [← Int.natAbs_mul, h]; norm_num
-- Exhibit all factors of $64$ and check every possible value of $x$
      rw [show Nat.divisors 64={1,2,4,8,16,32,64} by decide] at this
      simp at this; repeat rw [Int.natAbs_eq_iff] at this
      norm_num at this; repeat rw [or_assoc] at this
      rcases this with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx
-- Solving for $a$ in each case will finish the goal
      any_goals rw [← eq_sub_iff_add_eq] at hx; norm_num at hx; rw [hx] at h; norm_num at h
      · apply_fun (fun t => 15 - t) at h; norm_num at h; simp [h]
      · apply_fun (fun t => t + 17) at h; norm_num at h; simp [h]
      · apply_fun (fun t => 14 - t / 2) at h; norm_num at h; simp [h]
      · rw [mul_comm, ← neg_mul] at h; apply_fun (fun t => t / 2 + 18) at h; norm_num at h; simp [h]
      · apply_fun (fun t => 12 - t / 4) at h; norm_num at h; simp [h]
      · rw [mul_comm, ← neg_mul] at h; apply_fun (fun t => t / 4 + 20) at h; norm_num at h; simp [h]
      · rw [hx] at h; apply_fun (fun t => 8 - t / 8) at h; norm_num at h; simp [h]
      · rw [mul_comm, ← neg_mul] at h; apply_fun (fun t => t / 8 + 24) at h; norm_num at h; simp [h]
      · apply_fun (fun t => - t / 16 ) at h; norm_num at h; simp [h]
      · rw [mul_comm, ← neg_mul] at h; apply_fun (fun t => t / 16 + 32) at h; norm_num at h; simp [h]
      · rw [mul_comm] at h; apply_fun (fun t => - t / 32 - 16) at h; rw [← neg_mul] at h; norm_num at h; simp [h]
      · rw [mul_comm] at h; apply_fun (fun t => t / 32 + 48) at h; rw [← neg_mul] at h; norm_num at h; simp [h]
      · apply_fun (fun t => - t - 48) at h; norm_num at h; simp [h]
      rw [mul_comm] at h; apply_fun (fun t => t / 64 + 80) at h; rw [← neg_mul] at h; norm_num at h; simp [h]
-- Conversely, check that if $a$ equals any number in the set on RHS, the given equation has integer solutions
    intro ha; rcases ha with ha|ha|ha|ha|ha|ha|ha|ha; all_goals rw [ha]
    use -7; norm_num; use -6; norm_num; use -4; norm_num; use 0; norm_num
    use -16; norm_num; use -24; norm_num; use -40; norm_num; use -72; norm_num
  rw [SLa]; norm_num
import Mathlib

theorem algebra_9138_1 (a b c : ℝ) (h0 : a + b + c = 0) (h1 : a^2 + b^2 + c^2 = 6) :
a ≤ 2 := by
-- Rewrite assumptions by isolating $a$
  rw [add_assoc, add_eq_zero_iff_neg_eq] at h0
  rw [add_assoc, ← eq_sub_iff_add_eq'] at h1
-- Apply AM-GM inequality
  have := two_mul_le_add_pow_two b c
  rw [← add_le_add_iff_left (b^2+c^2)] at this
  rw [show b^2+c^2+2*b*c=(b+c)^2 by ring] at this
-- Plug in assumptions to the inequality to get an inequality on $a$
-- then solve for $a$
  rw [← h0, h1] at this; rw [neg_sq, ← two_mul, mul_sub] at this
  rw [le_sub_iff_add_le] at this; ring_nf at this
  rw [show (12:ℝ)=2^2*3 by norm_num] at this
  rw [mul_le_mul_iff_of_pos_right, sq_le_sq, abs_le] at this
  simp at this; linarith; norm_num

theorem algebra_9138_2 :
IsGreatest {a : ℝ | ∃ b c, a + b + c = 0 ∧ a ^ 2 + b ^ 2 + c ^ 2 = 6} 2 := by 
  constructor
  · -- Show 2 is in the set
    use -1, -1
    constructor <;> norm_num
  · -- Show no greater value is in the set
    intro a
    intro ha
    rcases ha with ⟨b, c, h0, h1⟩
    rw [add_assoc, add_eq_zero_iff_neg_eq] at h0
    rw [add_assoc, ← eq_sub_iff_add_eq'] at h1
-- Apply AM-GM inequality
    have := two_mul_le_add_pow_two b c
    rw [← add_le_add_iff_left (b^2+c^2)] at this
    rw [show b^2+c^2+2*b*c=(b+c)^2 by ring] at this
-- Plug in assumptions to the inequality to get an inequality on $a$
-- then solve for $a$
    rw [← h0, h1] at this; rw [neg_sq, ← two_mul, mul_sub] at this
    rw [le_sub_iff_add_le] at this; ring_nf at this
    rw [show (12:ℝ)=2^2*3 by norm_num] at this
    rw [mul_le_mul_iff_of_pos_right, sq_le_sq, abs_le] at this
    simp at this; linarith; norm_num
import Mathlib
set_option maxHeartbeats 0

open Finset Real

theorem inequalities_600067 (n : ℕ) (npos : 0 < n) (x : ℝ) (xpos : 0 < x) :
    ∑ k ∈ Icc 1 n, x ^ (k ^ 2) / k ≥ x ^ ((1 : ℝ) / 2 * n * (n + 1)) := by
  rw [ge_iff_le]; induction n with
  | zero => contradiction
  | succ s ihs =>
    by_cases hs : s ≤ 0
    · simp at hs; simp [hs]; norm_num
    specialize ihs (by omega); rw [sum_Icc_succ_top]; push_cast
    suffices : x ^ ((1 : ℝ) / 2 * (s + 1) * ((s + 1) + 1)) ≤
    x ^ ((1 : ℝ) / 2 * s * (s + 1)) + x ^ (s + 1) ^ 2 / (s + 1)
    · apply le_trans this; rw [add_le_add_iff_right]
      exact ihs
    rw [← rpow_natCast]; push_cast
    have : (1 : ℝ) / 2 * (s + 1) * (s + 1 + 1) =
    1 / 2 * s * (s + 1) + (1 / 2 * (s + 1)) * 2 := by ring
    rw [this, rpow_add]; replace this : ((s : ℝ) + 1) ^ 2 =
    1 / 2 * s * (s + 1) + (1 / 2 * (s + 1)) * (s + 2) := by ring
    rw [this, rpow_add, mul_div_assoc, ← mul_one_add]
    rw [mul_le_mul_left, rpow_mul]; nth_rw 2 [rpow_mul]
    set y := x ^ (((1 : ℝ) / 2) * (s + 1))
    have ypos : 0 < y := by positivity
    rcases le_or_lt y 1 with yle1|ygt1
    · apply le_add_of_le_of_nonneg
      apply rpow_le_one; any_goals positivity
      exact yle1
    nth_rw 2 [add_comm]; rw [rpow_add, mul_div_assoc]
    rcases le_or_lt 1 (y^(s : ℝ) / (s + 1)) with y'ge|y'lt
    · rw [add_comm]; apply le_add_of_le_of_nonneg
      nth_rw 1 [show y ^ (2 : ℝ) = y ^ (2 : ℝ) * 1 by simp]
      gcongr; simp
    rw [show (2:ℝ) = (2:ℕ) by rfl]; repeat rw [rpow_natCast]
    rw [mul_div, mul_comm, ← pow_add, ← sub_nonneg]
    let f : ℝ → ℝ := fun t => 1 + t ^ (s + 2) / (s + 1) - t ^ 2
    let a := (2 * ((s : ℝ) + 1) / (s + 2)) ^ (1 / (s : ℝ))
    have apos : 0 < a := by positivity
    have auxa : a ^ s = 2 * (s + 1) / (s + 2) := by
      dsimp [a]; rw [← rpow_natCast, ← rpow_mul]
      rw [one_div_mul_cancel, rpow_one]
      norm_cast; omega; positivity
    have fmono : MonotoneOn f (Set.Ici a) := by
      apply monotoneOn_of_deriv_nonneg
      · exact convex_Ici a
      · apply Continuous.continuousOn; dsimp [f]; continuity
      · apply Differentiable.differentiableOn
        dsimp [f]; apply Differentiable.sub
        apply Differentiable.add; exact differentiable_const 1
        apply Differentiable.div_const; exact differentiable_pow (s + 2)
        exact differentiable_pow 2
      simp [f]; intro t tgt; have tpos : 0 < t := by
        linarith only [tgt, apos]
      rw [deriv_sub, deriv_add, deriv_div_const]; simp
      rw [← pow_lt_pow_iff_left₀ _ _ (show s≠0 by omega)] at tgt
      rw [auxa, div_lt_iff₀] at tgt; nth_rw 2 [mul_comm]
      rw [pow_succ', mul_assoc, ← mul_div, mul_comm, mul_le_mul_left]
      rw [le_div_iff₀]; exact le_of_lt tgt
      any_goals positivity
      all_goals simp
    have fanti : AntitoneOn f (Set.Icc 0 a) := by
      apply antitoneOn_of_deriv_nonpos
      · apply convex_Icc
      · apply Continuous.continuousOn; dsimp [f]; continuity
      · apply Differentiable.differentiableOn
        dsimp [f]; apply Differentiable.sub
        apply Differentiable.add; exact differentiable_const 1
        apply Differentiable.div_const; exact differentiable_pow (s + 2)
        exact differentiable_pow 2
      simp [f]; intro t tgt tlt; have tpos : 0 < t := by
        linarith only [tgt, apos]
      rw [deriv_sub, deriv_add, deriv_div_const]; simp
      rw [← pow_lt_pow_iff_left₀ _ _ (show s≠0 by omega)] at tlt
      rw [auxa, lt_div_iff₀] at tlt; nth_rw 2 [mul_comm]
      rw [mul_comm, pow_succ', mul_assoc, ← mul_div, mul_le_mul_left]
      rw [div_le_iff₀]; exact le_of_lt tlt
      any_goals positivity
      all_goals simp
    have fmin : ∀ t : ℝ, 0 ≤ t → f a ≤ f t := by
      intro t tpos; rcases le_or_lt t a with tlea|altt
      · apply fanti; any_goals simp
        exact ⟨by linarith only [tpos], tlea⟩
        positivity; exact tlea
      apply fmono; any_goals simp
      all_goals exact le_of_lt altt
    specialize fmin y (le_of_lt ypos)
    suffices : 0 ≤ f a
    · apply le_trans this; dsimp [f]
      dsimp [f] at fmin; exact fmin
    dsimp [f]; rw [pow_add, mul_comm, auxa]
    rw [mul_div, div_div, ← mul_assoc, mul_div_mul_right]
    rw [sub_nonneg, ← sub_le_iff_le_add, ← mul_div, ← mul_one_sub]
    rw [one_sub_div, add_sub_cancel_right]
    rw [← le_div_iff₀, one_div_div, ← one_add_div]
    rw [← pow_le_pow_iff_left₀ _ _ (show s≠0 by omega)]
    rw [← pow_mul, mul_comm, pow_mul, auxa]
    rw [show 2*((s:ℝ)+1) = 2*(s+2)-2 by ring, ← div_sub_div_same]
    rw [mul_div_cancel_right₀]; by_cases hs : s < 2
    · replace hs : s = 1 := by omega
      simp [hs]; norm_num
    suffices : (2 : ℝ) ^ 2 ≤ (1 + 2 / s) ^ s
    · apply le_trans _ this; gcongr
      field_simp; ring_nf; positivity
      rw [← sub_nonneg]; ring_nf; positivity
    rw [add_pow, show s+1 = (s-2)+3 by omega, sum_range_add]
    simp [show range 3 = {0, 1, 2} by rfl]
    rw [show s-(s-2) = 2 by omega, show s-(s-2+1) = 1 by omega, pow_one]
    rw [show (s-2+2) = s by omega, Nat.sub_self, pow_zero, one_mul]
    rw [Nat.choose_symm, Nat.choose_two_right]
    rw [show s-2+1 = s-1 by omega, Nat.choose_symm, Nat.choose_one_right]
    rw [Nat.choose_self, div_mul_cancel₀]; norm_num
    rw [show (4:ℝ) = 1+3 by norm_num, ← add_assoc, add_le_add_iff_right]
    rw [add_comm]; apply le_add_of_le_of_nonneg
    · rw [Nat.cast_div]; push_cast
      rw [Nat.cast_sub]; push_cast; field_simp
      rw [le_div_iff₀, ← sub_nonneg]; ring_nf
      rw [neg_add_eq_sub, sub_nonneg]; norm_cast
      rw [show s*4 = s*2*2 by ring, pow_two]; gcongr
      any_goals omega
      norm_cast; simp; apply Nat.pow_pos; omega
      rcases Nat.even_or_odd' s with ⟨k, hk|hk⟩
      · rw [hk, mul_assoc]; simp
      rw [mul_comm]; simp [hk, mul_assoc]
      simp
    apply sum_nonneg; intros; any_goals positivity
    any_goals simp
    any_goals omega
    apply div_pos; simp; omega
    positivity
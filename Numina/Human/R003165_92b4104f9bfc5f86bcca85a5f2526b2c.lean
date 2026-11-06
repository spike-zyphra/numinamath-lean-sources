import Mathlib
open Finset Set Real
noncomputable section

-- Defines the number of real roots of a quadratic polynomial based on its discriminant.
def real_roots (a b c : ℝ) : ℕ :=
  if a ≠ 0 then
    if discrim a b c > 0 then 2
    else if discrim a b c = 0 then 1
    else 0
  else
    if b ≠ 0 then 1
    else if c = 0 then 1
    else 0

-- Proves a contradiction from non-negative discriminants of three quadratic polynomials.
lemma discrim_contradiction (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (h_disc1 : discrim a b c ≥ 0) (h_disc2 : discrim b c a ≥ 0) (h_disc3 : discrim c a b ≥ 0) :
  (a * b * c)^2 ≥ 64 * (a * b * c)^2 := by
  have h₁ : discrim a b c = b^2 - 4*a*c := rfl
  have h₂ : discrim b c a = c^2 - 4*b*a := rfl
  have h₃ : discrim c a b = a^2 - 4*c*b := rfl
  have h_ineq1 : b^2 ≥ 4*a*c := by linarith
  have h_ineq2 : c^2 ≥ 4*b*a := by linarith
  have h_ineq3 : a^2 ≥ 4*c*b := by linarith
  have : (a^2) * (b^2) * (c^2) ≥ (4 * c * b) * (4 * a * c) * (4 * b * a) := by
    have : (a^2) * (b^2) ≥ (4*c*b) * (4*a*c) := by
      apply mul_le_mul
      · linarith
      · linarith
      nlinarith [ha,hb,hc]
      simp [sq_nonneg]
    have h_4ba_pos: 0 ≤ 4 * b * a := by nlinarith
    have h_sq_pos: 0 ≤ a ^ 2 * b ^ 2 := by nlinarith
    apply mul_le_mul
    · exact this
    · linarith
    · exact h_4ba_pos
    · exact h_sq_pos
  have h_right : (4 * c * b) * (4 * a * c) * (4 * b * a) = 64 * (a * b * c)^2 := by
    simp [pow_two]
    ring
  have h_left : (a^2) * (b^2) * (c^2) = (a * b * c)^2 := by
    simp [pow_two]
    ring
  rw [h_left, h_right] at this
  exact this

/-1. Let $a, b$, and $c$ be positive real numbers. Determine the largest total number of real roots that the following three polynomials may have among them: $a x^{2}+b x+c, b x^{2}+c x+a$, and $c x^{2}+a x+b$.-/
theorem number_theory_158421 :
  IsGreatest {n | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧
    n = real_roots a b c + real_roots b c a + real_roots c a b} 4 := by
  apply And.intro
  · -- Prove that $4$ is attainable.
    have h_four_attainable : 4 ∈ {n | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧
      n = real_roots a b c + real_roots b c a + real_roots c a b} := by
      use 1, 5, 6
      constructor
      · simp
      · constructor
        · simp
        · constructor
          · simp
          · have h_r1 : real_roots 1 5 6 = 2 := by simp [real_roots, discrim]; norm_num
            have h_r2 : real_roots 5 6 1 = 2 := by simp [real_roots, discrim]; norm_num
            have h_r3 : real_roots 6 1 5 = 0 := by simp [real_roots, discrim]; norm_num
            simp [h_r1, h_r2, h_r3]
    exact h_four_attainable
  · -- Prove that three polynomials cannot each have $2$ roots.
    have h_not_all_two_roots : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
      ¬(real_roots a b c = 2 ∧ real_roots b c a = 2 ∧ real_roots c a b = 2) := by
      intros a b c ha hb hc h_all_two
      have h_disc1 : discrim a b c > 0 := by
        have h_r1_eq_2 : real_roots a b c = 2 := h_all_two.1
        unfold real_roots at h_r1_eq_2
        split_ifs at h_r1_eq_2 with h_a h_disc h_disc_zero
        · exact h_disc
        · contradiction
        · contradiction
        · contradiction
      have h_disc2 : discrim b c a > 0 := by
        have h_r2_eq_2 : real_roots b c a = 2 := h_all_two.2.1
        unfold real_roots at h_r2_eq_2
        split_ifs at h_r2_eq_2 with h_b h_disc h_disc_zero
        · exact h_disc
        · contradiction
        · contradiction
        · contradiction
      have h_disc3 : discrim c a b > 0 := by
        have h_r3_eq_2 : real_roots c a b = 2 := h_all_two.2.2
        unfold real_roots at h_r3_eq_2
        split_ifs at h_r3_eq_2 with h_c h_disc h_disc_zero
        · exact h_disc
        · contradiction
        · contradiction
        · contradiction
      have h_abc_pos : a * b * c > 0 := by apply mul_pos (mul_pos ha hb) hc
      have : (a * b * c)^2 > 0 := by apply pow_pos h_abc_pos 2
      have h_product := discrim_contradiction a b c ha hb hc
        (by linarith [h_disc1]) (by linarith [h_disc2]) (by linarith [h_disc3])
      have : (a * b * c)^2 / (a * b * c)^2 ≤ 64 * (a * b * c)^2 / (a * b * c)^2 := by nlinarith
      have : 1 ≤ 64 := by simp [this]
      linarith
    -- Prove that the total number of real roots is at most $4$.
    have h_upper_bound : ∀ n ∈ {n | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧
      n = real_roots a b c + real_roots b c a + real_roots c a b}, n ≤ 4 := by
      intros n hn
      obtain ⟨a, b, c, ha, hb, hc, h_n⟩ := hn
      have h_r1_le_2 : real_roots a b c ≤ 2 := by simp [real_roots]; split_ifs <;> norm_num
      have h_r2_le_2 : real_roots b c a ≤ 2 := by simp [real_roots]; split_ifs <;> norm_num
      have h_r3_le_2 : real_roots c a b ≤ 2 := by simp [real_roots]; split_ifs <;> norm_num
      have h_not_all_two := h_not_all_two_roots a b c ha hb hc
      have h_sum_le_4 : real_roots a b c + real_roots b c a + real_roots c a b ≤ 4 := by
        by_contra h_gt_4
        have h_sum_ge_5 : real_roots a b c + real_roots b c a + real_roots c a b ≥ 5 := by nlinarith
        have h_all_ge_1 : real_roots a b c ≥ 1 ∧ real_roots b c a ≥ 1 ∧ real_roots c a b ≥ 1 := by omega
        have h_disc1 : discrim a b c ≥ 0 := by
          have : real_roots a b c ≥ 1 := h_all_ge_1.1
          simp [real_roots, ha] at this
          split_ifs at this <;> (try linarith)
        have h_disc2 : discrim b c a ≥ 0 := by
          have : real_roots b c a ≥ 1 := h_all_ge_1.2.1
          simp [real_roots, hb] at this
          split_ifs at this <;> (try linarith)
        have h_disc3 : discrim c a b ≥ 0 := by
          have : real_roots c a b ≥ 1 := h_all_ge_1.2.2
          simp [real_roots, hc] at this
          split_ifs at this <;> (try linarith)
        have h_abc_pos : a * b * c > 0 := by apply mul_pos (mul_pos ha hb) hc
        have : (a * b * c)^2 > 0 := by apply pow_pos h_abc_pos 2
        -- Derive a contradiction by using the lemma.
        have h_product := discrim_contradiction a b c ha hb hc h_disc1 h_disc2 h_disc3
        have : (a * b * c)^2 / (a * b * c)^2 ≤ 64 * (a * b * c)^2 / (a * b * c)^2 := by nlinarith
        have : 1 ≤ 64 := by simp [this]
        linarith
      rw [h_n]
      exact h_sum_le_4
    exact h_upper_bound

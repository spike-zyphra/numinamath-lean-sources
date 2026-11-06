import Mathlib

theorem algebra_9443_1 (k : ℝ) (h : ∃ x y, x ≠ y ∧ (k - 2) * x ^ 2 - 4 * x + 4 = 0 ∧ (k - 2) * y ^ 2 - 4 * y + 4 = 0) :
k ≤ 3 ∧ k ≠ 2 ∧ k ≠ 3 := by
-- Introduce two roots of the quadratic equation
  rcases h with ⟨x1, x2, h12, h1, h2⟩
-- Prove that $k$ can't be $2$ or $3$ by solving for $x1$ and $x2$
  have kne2 : k ≠ 2 := by
    intro h'; simp [h'] at h1 h2
    rw [← h1] at h2; simp at h2; symm at h2; contradiction
  have kne3 : k ≠ 3 := by
    intro h'; simp [h'] at h1 h2; ring_nf at h1 h2
    rw [show 4 - x1 * 4 + x1 ^ 2 = (2 - x1) ^ 2 by ring] at h1
    rw [show 4 - x2 * 4 + x2 ^ 2 = (2 - x2) ^ 2 by ring] at h2
    simp at h1 h2; simp [← h1] at h2; symm at h2; contradiction
-- Prove that the discriminant of the quadratic equation is nonnegative
-- by applying the key lemma quadratic_eq_zero_iff_discrim_eq_sq
  rw [pow_two, ← mul_assoc, sub_eq_add_neg, ← neg_mul, mul_assoc, quadratic_eq_zero_iff_discrim_eq_sq] at h1
  have discnonneg : 0 ≤ discrim (k - 2) (-4) 4 := by rw [h1]; apply pow_two_nonneg
-- Solve for bounds on $k$
  rw [discrim] at discnonneg; ring_nf at discnonneg; simp at discnonneg
  rw [show (48:ℝ)=3*16 by norm_num, mul_le_mul_right] at discnonneg
-- Prove our final goals
  norm_num; constructor; assumption
  constructor; assumption; assumption; norm_num
  rw [sub_ne_zero]; assumption

theorem algebra_9443_2 : IsGreatest {m : ℤ | ∃ x y : ℝ, x ≠ y ∧
(m - 2) * x ^ 2 - 4 * x + 4 = 0 ∧ (m - 2) * y ^ 2 - 4 * y + 4 = 0} 1 := by
-- Split into two goals: 1 belongs to the set, and any element in the set ≤ 1
  constructor
  · -- Show 1 is in the set by using two real roots
    use -2 + 2 * Real.sqrt 2, -2 - 2 * Real.sqrt 2
    constructor
    · -- Show -2 + 2 * Real.sqrt 2 ≠ -2 - 2 * Real.sqrt 2
      by_contra h
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (2 : ℝ) by norm_num)]
    constructor
    · -- Show (1 - 2) * (-2 + 2 * Real.sqrt 2) ^ 2 - 4 * (-2 + 2 * Real.sqrt 2) + 4 = 0
      ring_nf
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (2 : ℝ) by norm_num)]
    · -- Show (1 - 2) * (-2 - 2 * Real.sqrt 2) ^ 2 - 4 * (-2 - 2 * Real.sqrt 2) + 4 = 0
      ring_nf
      nlinarith [Real.sqrt_pos.mpr (show (0: ℝ) < 2 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show any integer m in the set is ≤ 1
    intro m hm
    rcases hm with ⟨x1, x2, h12, h1, h2⟩
    -- Apply theorem algebra_9443_1
    have hmle3 := algebra_9443_1 m ⟨x1, x2, h12, h1, h2⟩
    have hm1 : m ≤ 3 := by
      by_contra h2
      push_neg at h2
      have h3 : (m: ℝ) > (3: ℝ) := by exact_mod_cast h2
      linarith
    have hmne2 : m ≠ 2 := by
      by_contra h2
      have h2' : (m: ℝ) = (2: ℝ) := by exact_mod_cast h2
      tauto
    have hmne3 : m ≠ 3 := by
      by_contra h2
      have h2' : (m: ℝ) = (3: ℝ) := by exact_mod_cast h2
      tauto
    by_contra h
    push_neg at h
    have h5 : m = 2 ∨ m = 3 := by omega
    rcases h5 with (h5 | h5)
    · -- Show m=2 is false
      tauto
    · -- Show m=3 is false
      tauto
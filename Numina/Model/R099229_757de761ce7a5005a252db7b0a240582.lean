import Mathlib

open Real

-- lemma : if $a ^ 2 + b ^ 2 = 1$, then there exists $\theta$ where $a = \cos \theta$ and $b = \sin \theta$
lemma l_9151 {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ∃ θ, a = cos θ ∧ b = sin θ := by
  have rab : (-1 ≤ a ∧ a ≤ 1) ∧ (-1 ≤ b ∧ b ≤ 1) := by
    constructor
    all_goals
      apply abs_le.mp
      apply (sq_le_one_iff_abs_le_one _).mp
      linarith [sq_nonneg b, sq_nonneg a]
  set θ := arccos a
  have : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg a) (arccos_le_pi a)
  have ra : a = cos θ := by
    rw [Real.cos_arccos]
    all_goals simp only [rab]
  have rb : |b| = |sin θ| := by
    apply (sq_eq_sq_iff_abs_eq_abs _ _).mp
    rw [sin_sq θ, ← ra]
    linarith
  rcases le_or_lt 0 a with ha | ha
  . rcases le_or_lt 0 b with hb | hb
    . use θ
      simp [ra]
      repeat rw [abs_of_nonneg] at rb
      all_goals linarith
    . use -θ
      simp [ra]
      rw [abs_of_neg, abs_of_nonneg] at rb
      all_goals linarith
  . rcases le_or_lt 0 b with hb | hb
    . use θ
      simp [ra]
      repeat rw [abs_of_nonneg, abs_of_nonneg] at rb
      all_goals linarith
    . use -θ
      simp [ra]
      rw [abs_of_neg, abs_of_nonneg] at rb
      all_goals linarith


theorem algebra_9151 :
    IsGreatest {v | ∃ x y : ℝ, (x - 3)^2 + (y - 3)^2 = 8 ∧ x + y = v} 10 := by

  constructor
  · -- Show that 10 can be obtained, i.e., (5, 5) is a solution
    use 5, 5
    norm_num
  · -- Show that 10 is the greatest value
    intro v hv
    rcases hv with ⟨x, y, h_eq, h_sum⟩
    nlinarith [sq_nonneg (x - 5), sq_nonneg (y - 5), sq_nonneg (x - y)]
import Mathlib
open Real Set

theorem algebra_9176 {f : ℝ → ℝ} (hf : f = λ x => log (-x^2 + 2 * x)) :
    StrictMonoOn f (Set.Ioc 0 1) ∧ StrictAntiOn f (Set.Ico 1 2) := by
  constructor
  · -- Prove that $f$ is strictly monotone on $(0, 1]$
    intros x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    rcases hx with ⟨hx0, hx1⟩
    rcases hy with ⟨hy0, hy1⟩
    have h1 : -x^2 + 2 * x > 0 := by
      nlinarith
    have h2 : -y^2 + 2 * y > 0 := by
      nlinarith
    have h3 : -x^2 + 2 * x < -y^2 + 2 * y := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), hxy]
    have h4 : log (-x^2 + 2 * x) < log (-y^2 + 2 * y) := by
      apply Real.log_lt_log
      all_goals nlinarith
    linarith
  · -- Prove that $f$ is strictly antitone on $[1, 2)$
    intros x hx y hy hxy
    rw [hf]
    simp at hx hy ⊢
    rcases hx with ⟨hx1, hx2⟩
    rcases hy with ⟨hy1, hy2⟩
    have h1 : -x^2 + 2 * x > 0 := by
      nlinarith
    have h2 : -y^2 + 2 * y > 0 := by
      nlinarith
    have h3 : -x^2 + 2 * x > -y^2 + 2 * y := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), hxy]
    have h4 : log (-x^2 + 2 * x) > log (-y^2 + 2 * y) := by
      apply Real.log_lt_log
      all_goals nlinarith
    linarith
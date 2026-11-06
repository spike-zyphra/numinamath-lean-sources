import Mathlib

open Real Set
open scoped BigOperators

/- Part I: Given the function $f(x) = \cos 2x + a\cos x$, when $a = 2$, the minimum value of $f(x)$ is ____ -/
theorem algebra_9088_1 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => cos (2 * x) + a * cos x) (ha : a = 2) : IsLeast (range f) (-3/2) := by
  -- first part of the problem. when a=1, minimum value of f(x) is _.
  -- when a=1, we can prove f(x) = 2(cosx+1/2)^2-3/2
  have hf': f = (fun x => 2 * (cos x + 1/2)^2 + (-3/2:ℝ)) := by
    rw [hf, ha]
    funext x
    have: cos (2*x) = 2*(cos x)^2 - 1 := cos_two_mul x
    rw [this]
    ring
  rw [IsLeast]
  -- show f(x) ≤ 1
  have h2: (-3/2:ℝ) ∈ lowerBounds (range f) := by
    rw [lowerBounds]
    simp
    intro x
    rw [hf']
    simp
    have: (cos x + 2⁻¹) ^ 2 ≥ 0 := sq_nonneg (cos x + 2⁻¹)
    have: 0 ≤ 2 * (cos x + 2⁻¹) ^ 2 := by linarith [this]
    linarith [this]
  have h3: (-3/2) ∈ range f := by
    simp
    -- when cosx+1/2 = 0, f(x) reaches minimum.
    -- so use arccos (-1/2) here
    use arccos (-1/2)
    rw [hf']
    simp
    have: cos (arccos (-1 / 2)) = -1/2 := by
      have ht1: -1 ≤ (-1/2:ℝ) := by norm_num
      have ht2: (-1/2:ℝ) ≤ 1 := by norm_num
      apply cos_arccos ht1 ht2
    rw [this]
    ring
  exact ⟨h3, h2⟩

/- Part II: Given the function $f(x) = \cos 2x + a\cos x$, if the maximum value of $f(x)$ is $2$, then the value of $a$ is ____.  -/
theorem algebra_9088_2 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => cos (2 * x) + a * cos x) (hmax: IsGreatest (range f) 2): a = 1 ∨ a = -1 := by
  -- second part of the problem. when maximum value of f(x) is 2, a = _.
  rw [IsGreatest, upperBounds] at hmax
  simp at hmax
  rcases hmax with ⟨fex, fmax⟩
  -- show f(x) = 2(cosx+a/4)^2-a^2/8
  have hf': f = (fun x => 2 * (cos x + a/4)^2 -1 - a^2/8) := by
    rw [hf]
    funext x
    have: cos (2*x) = 2*(cos x)^2 - 1 := cos_two_mul x
    rw [this]
    ring
  -- maximum of (cosx+a/4)^2 is (1+a/4)^2 or (1-a/4)^2, depends on the sign of a.
  by_cases ha: 0 ≤ a
  have hfmax: ∀x:ℝ, f x ≤ 2*(1+a/4)^2 - 1 - a^2/8 := by
    rw [hf']
    intro x
    simp
    have h1: -(1 + a / 4) ≤ cos x + a / 4 := by
      have: (-1:ℝ) ≤ cos x := neg_one_le_cos x
      linarith [ha, this]
    have h2: cos x + a / 4 ≤ 1 + a / 4 := by
      have: cos x ≤ 1 := cos_le_one x
      linarith [this]
    apply sq_le_sq' h1 h2
  have hfex: ∃x:ℝ, f x = 2*(1+a/4)^2 - 1 - a^2/8 := by
    -- if 0≤a, then f(x) reaches maximum when cosx = 1.
    use 0
    rw [hf']
    simp
  -- maximum of f(x) is 2*(1+a/4)^2 - 1 - a^2/8 and 2, then they must be equal
  have h1: 2*(1+a/4)^2 - 1 - a^2/8 ≤ 2 := by
    rcases hfex with ⟨x0, h1x0⟩
    rcases fmax x0 with h2x0
    rwa [h1x0] at h2x0
  have h2: 2 ≤ 2*(1+a/4)^2 - 1 - a^2/8 := by
    rcases fex with ⟨x0, h1x0⟩
    rcases hfmax x0 with h2x0
    rwa [h1x0] at h2x0
  have aeq: a = 1 := by
    have ht1: 2 * (1 + a / 4) ^ 2 - 1 - a ^ 2 / 8 = 2 := eq_of_le_of_le h1 h2
    have ht2: 2 * (1 + a / 4) ^ 2 - 1 - a ^ 2 / 8 = a+1 := by ring
    rw [ht2] at ht1
    have: (1:ℝ)=2-1 := by norm_num
    rw [this, ← ht1]
    ring
  left
  exact aeq
  push_neg at ha
  -- now a<0, we can show f(x) reaches maximum when cosx = -1
  have hfmax: ∀x:ℝ, f x ≤ 2*(-1+a/4)^2 - 1 - a^2/8 := by
    rw [hf']
    intro x
    simp
    have: |cos x + a / 4| ≤ |-1 + a / 4| := by
      have ht1: |-1+a/4| = - (-1+a/4) := by
        have: -1+a/4 < 0 := by linarith [ha]
        exact abs_of_neg this
      rw [ht1]
      rw [abs_le]
      simp
      have ht2: -1 ≤ cos x := neg_one_le_cos x
      have ht3:  a / 4 + (cos x + a / 4) ≤ 1 := by
        have: cos x ≤ 1 := cos_le_one x
        linarith [ha, this]
      exact ⟨ht2,ht3⟩
    apply sq_le_sq.mpr this
  have hfex: ∃x:ℝ, f x = 2*(-1+a/4)^2 - 1 - a^2/8 := by
    -- if a<0, then f(x) reaches maximum when cosx = -1.
    use (Real.pi)
    rw [hf']
    simp
  -- maximum of f(x) is 2*(-1+a/4)^2 - 1 - a^2/8 and 2, then they must be equal.
  have heq:  2 * (-1 + a / 4) ^ 2 - 1 - a ^ 2 / 8 = -a+1 := by ring
  rw [heq] at hfmax
  rw [heq] at hfex
  have h1: (-a+1) ≤ 2 := by
    rcases hfex with ⟨x0,h1x0⟩
    rcases fmax x0 with h2x0
    rwa [h1x0] at h2x0
  have h2: 2 ≤ (-a+1):= by
    rcases fex with ⟨x0, h1x0⟩
    rcases hfmax x0 with h2x0
    rwa [h1x0] at h2x0
  have aeq: a = -1 := by
    have: -a+1=2 := eq_of_le_of_le h1 h2
    linarith [this]
  right
  exact aeq
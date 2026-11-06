import Mathlib

open Real Set
open scoped BigOperators

/- Find the maximum value of the function $y=3\sin x+2 \sqrt {2+2\cos 2x}$. -/
theorem algebra_9063 (f : ℝ → ℝ) (hf : f = λ x => 3 * sin x + 2 * sqrt (2 + 2 * cos (2 * x))) : IsGreatest (range f) 5 := by
  -- at very first, we show f(x) = 3sinx+4√(cos x ^2)
  have hf': f = (fun x => 3*sin x + 4*√(cos x ^2)) := by
    rw [hf]
    funext x
    have h1:  2 * √(2 + 2 * cos (2 * x)) = 4 * √(cos x ^2) := by
      have: cos (2*x) = 2*cos x ^2 -1 := cos_two_mul x
      rw [this]
      have: 2 + 2 * (2 * cos x ^ 2 - 1) = 4 * cos x ^2 := by ring
      rw [this]
      have: √(4 * cos x ^ 2) = √4 * √(cos x ^2) := by simp
      rw [this]
      have: √4 = 2 := by
        have ht1: (4:ℝ) = 2^2 := by ring
        rw [ht1]
        have ht2: 0 ≤ (2:ℝ) := by norm_num
        exact sqrt_sq ht2
      rw [this]
      ring
    rw [h1]
  rw [IsGreatest, upperBounds]
  -- prove f(x) ≤ 5
  have hfmax: 5 ∈ {x | ∀ ⦃a : ℝ⦄, a ∈ range f → a ≤ x} := by
    simp
    rw [hf']
    simp
    intro x
    -- now, we show 3 * sin x + 4 * √(cos x ^ 2) ≤ 5 by using a kind of Cauchy-Schwarz inequality
    have schwarz_ineq: (3 * sin x + 4 * √(cos x ^ 2))^2 ≤ 25 := by
      have ht: √(cos x ^ 2) ^ 2 = cos x ^ 2 := by
          have: 0 ≤ cos x ^2 := sq_nonneg (cos x)
          apply sq_sqrt this
      have h1: (3 * sin x + 4 * √(cos x ^ 2))^2 = 9*sin x ^2 + 16 * cos x ^2 + 2* (3 * sin x) * (4 * √(cos x ^2)) := by
        ring_nf
        simp [ht]
      have h2: 2* (4 * sin x) * (3 * √(cos x ^2)) ≤ (4*sin x)^2 + (3 * √(cos x ^2))^2 := by
        have: 2* (4 * sin x) * (3 * √(cos x ^2)) - ((4*sin x)^2 + (3 * √(cos x ^2))^2) ≤ 0 := by
          have: 2* (4 * sin x) * (3 * √(cos x ^2)) - ((4*sin x)^2 + (3 * √(cos x ^2))^2) = -((4*sin x)-(3*√(cos x ^2)))^2 := by
            ring_nf
          rw [this]
          have: 0 ≤ (4 * sin x - 3 * √(cos x ^ 2)) ^ 2 := sq_nonneg (4 * sin x - 3 * √(cos x ^ 2))
          linarith [this]
        linarith [this]
      have h3: (3 * sin x + 4 * √(cos x ^ 2)) ^ 2 ≤ ( 9 * sin x ^ 2 + 16 * cos x ^ 2) + ((4 * sin x) ^ 2 + (3 * √(cos x ^ 2)) ^ 2) := by linarith [h1, h2]
      have h4:  9 * sin x ^ 2 + 16 * cos x ^ 2 + ((4 * sin x) ^ 2 + (3 * √(cos x ^ 2)) ^ 2) = 25 := by
        have: (1:ℝ) = sin x^2 + cos x^2 := by
          exact Eq.symm (sin_sq_add_cos_sq x)
        rw [← mul_one 25, this]
        ring_nf
        simp [ht]
        ring
      rwa [h4] at h3
    have: (25:ℝ) = 5*5 := by norm_num
    rw [this] at schwarz_ineq
    have h1: 0 ≤ (5:ℝ) := by norm_num
    have: (3 * sin x + 4 * √(cos x ^ 2)) ^ 2 = (3 * sin x + 4 * √(cos x ^ 2)) * (3 * sin x + 4 * √(cos x ^ 2)) := by ring
    rw [this] at schwarz_ineq
    apply nonneg_le_nonneg_of_sq_le_sq h1 schwarz_ineq
  -- prove ∃x, f(x)=5. by Cauchy-Schwarz inequality, the equal sign takes when 4 * sin x = 3 * √(cos x ^ 2). we use such x that 4sinx = 3cosx.
  have hfex:  5 ∈ range f := by
    simp
    use arcsin (3/5)
    rw [hf']
    simp
    have h1: sin (arcsin (3/5)) = (3/5:ℝ) := by
        have ht1: -(1:ℝ) ≤ 3/5 := by norm_num
        have ht2: 3/5 ≤ (1:ℝ) := by norm_num
        apply sin_arcsin ht1 ht2
    have h2: √(cos (arcsin (3 / 5)) ^ 2) = 4/5 := by
      have ht1: (cos (arcsin (3 / 5)) ^ 2) = 1 - (sin (arcsin (3/5)) ^2) := by
        exact cos_sq' (arcsin (3 / 5))
      rw [h1] at ht1
      have ht2:  1 - (3 / 5) ^ 2 = (4/5: ℝ)^2 := by ring
      rw [ht1, ht2]
      have ht3: 0 ≤ (4/5:ℝ) := by norm_num
      apply sqrt_sq ht3
    rw [h1, h2]
    ring
  exact ⟨hfex, hfmax⟩
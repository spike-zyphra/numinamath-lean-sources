import Mathlib

/- Let $n$ be the answer to this problem. Box $B$ initially contains $n$ balls, and Box $A$ contains half as many balls as Box $B$. After 80 balls are moved from Box $A$ to Box $B$, the ratio of balls in Box $A$ to Box $B$ is now $\frac{p}{q}$, where $p, q$ are positive integers with $\operatorname{gcd}(p, q)=1$. Find $100 p+q$.-/
theorem algebra_610398 :
    {n | ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ 2 ∣ n ∧ n / 2 > 80 ∧ (n / 2 - 80) / (n + 80) = (p / q : ℝ) ∧ Nat.gcd p q = 1 ∧ n = 100 * p + q} = {720} := by
  ext n
  apply Iff.intro
  . -- Show that the condition of the problem implies that 100p + q = 720.
    simp
    intro p hp q hq h₀ h₁ h₂ hn
    -- Substitute n = 100p + q into the equation.
    rw [hn] at h₁
    field_simp at h₁
    -- Simplify the equation and rewrite as a quadratic equation in p.
    replace h₁ : 2601 * p ^ 2 - 7680 * p + 6400 = (q - 80 + 49 * p : ℝ) ^ 2 := by
      linarith
    -- The discriminant of this quadratic equation has to be a perfect square.
    have h₁' := h₁
    let t' : ℤ := q - 80 + 49 * p
    rw [show (q - 80 + 49 * p : ℝ) = t' by simp [t']] at h₁
    let t := t'.natAbs
    rw [show (t' ^ 2 : ℝ) = (t' ^ 2 : ℤ) by simp, show t' ^ 2 = t ^ 2 by simp [t, Int.natAbs_sq]] at h₁
    simp at h₁
    -- Show that p < 26.
    have h₃ : p < 26 := by
      -- Assume on the contrary that p ≥ 26, then the above expression cannot be a perfect square.
      by_contra! h₃
      rify at h₃
      -- Show that (51p - 76)² < 2601p² - 7680p + 6400 < (51p - 75)².
      have h₄ : (51 * p - 76 : ℝ) ^ 2 < t ^ 2 := by
        linarith
      have h₅ : t ^ 2 < (51 * p - 75 : ℝ) ^ 2 := by
        linarith
      rw [sq_lt_sq₀ (by linarith) (by linarith)] at h₄ h₅
      linarith only [show (51 * p - 76 : ℤ) < t by rify; nlinarith, show t < (51 * p - 75 : ℤ) by rify; nlinarith]
    -- Show that for p < 26, only p = 2 or 7 satisfies the condition (making 2601p² - 7680p + 6400 a perfect square).
    replace h₁ : IsSquare (2601 * p ^ 2 - 7680 * p + 6400 : ℤ) := by
      use t
      rify
      linarith only [h₁]
    have h₄ : p = 2 ∨ p = 7 := by
      interval_cases p
      -- For p = 2 or 7, directly gives the answer.
      <;> try tauto
      all_goals
        -- For other cases, use native_decide to show that the number is not a perfect square.
        absurd h₁
        norm_num
        native_decide
    -- Consider the cases p = 2 and p = 7.
    rcases h₄ with (h₄ | h₄)
    . -- Note that (p, q) = (2, 20) does not satisfy the coprime condition, hence this case is eliminated.
      have h₅ : q = 20 := by
        -- Substitute p = 2 into the equation.
        rw [h₄] at h₁'
        replace h₁' : (q + 18) ^ 2 = 38 ^ 2 := by
          rify
          norm_num at h₁'
          linarith only [h₁']
        rw [sq_eq_sq₀ (by positivity) (by norm_num)] at h₁'
        -- Show that q = 20.
        omega
      norm_num [h₄, h₅] at h₂
    . -- We have (p, q) = (7, 20), which is the solution we want.
      have h₅ : q = 20 := by
        -- Substitute p = 7 into the equation.
        rw [h₄] at h₁'
        replace h₁' : (q + 263) ^ 2 = 283 ^ 2 := by
          rify
          norm_num at h₁'
          linarith only [h₁']
        rw [sq_eq_sq₀ (by positivity) (by norm_num)] at h₁'
        -- Show that q = 20.
        omega
      norm_num [hn, h₄, h₅]
  . -- Show that 720 is attainable.
    simp
    intro hn
    use 7, by norm_num, 20
    norm_num [hn]
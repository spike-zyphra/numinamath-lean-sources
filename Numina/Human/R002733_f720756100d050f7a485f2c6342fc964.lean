import Mathlib
open Real
/- 4. Determine all ordered triples $(a, b, c)$ of real numbers such that the function $f: \mathbb{R} \rightarrow \mathbb{R}$, defined by

$$
f(x)=\sin \left(a x^{2}+b x+c\right)
$$

is even. (A function $f$ is said to be even if $f(x)=$ $f(-x)$ for all $x$. -/
theorem algebra_105511 : {(a, b, c) : ℝ × ℝ × ℝ | ∀ x : ℝ, sin (a * x ^ 2 + b * x + c) = sin (a * (-x) ^ 2 + b * (-x) + c)} = {(a, b, c) : ℝ × ℝ × ℝ | b = 0 ∨ (a = 0 ∧ (∃ k : ℤ, c = π / 2 + k * π))}:= by
  -- Prove set equality by showing membership equivalence
  ext ⟨a, b, c⟩
  constructor
  -- Forward direction: if f is even, then b = 0 or (a = 0 and c = π/2 + kπ)
  .
    intro h
    simp at h
    -- Case analysis on whether b = 0
    by_cases h1 : b = 0
    -- Case 1: b = 0, then we're done
    .
      subst b
      simp
    -- Case 2: b ≠ 0, we need to show a = 0 and c has the required form
    .
      -- Key lemma: for small positive x, cos(ax² + c) = 0
      have h2 : ∀ x : ℝ, 0 < x → x < π / |b| → cos (a * x ^ 2 + c) = 0:= by
        intro x h2 h3
        specialize h x
        -- Transform the evenness condition into a difference of sines
        replace h : sin (a * x ^ 2 + b * x + c) - sin (a * x ^ 2 - b * x + c) = 0:= by
          ring_nf at h ⊢
          linarith
        -- Apply sine difference formula
        rw [Real.sin_sub_sin (a * x ^ 2 + b * x + c) (a * x ^ 2 - b * x + c)] at h
        ring_nf at h
        simp at h
        rcases h with h | h
        -- Case where sin(bx) = 0
        .
          apply Real.sin_eq_zero_iff.1 at h
          rcases h with ⟨n, hn⟩
          have g1:= pi_pos
          have h:= hn
          -- Show that |n| < 1, so n = 0, leading to contradiction
          replace hn : |n * π| = |x * b|:= by rw [hn]
          rw [show |n * π| = |↑n| * |π| by exact abs_mul ↑n π] at hn
          rw [show |x * b| = |x| * |b| by exact abs_mul x b] at hn
          rw [abs_of_pos h2] at hn
          rw [abs_of_pos g1] at hn
          replace hn : |n| = x * (|b| / π):= by
            field_simp
            linarith
          have g2 : |b| > 0:= by positivity
          replace h1 : |b| / π > 0:= by positivity
          replace h3 : x * (|b| / π) < π / |b| * (|b| / π):= by exact (mul_lt_mul_iff_of_pos_right h1).mpr h3
          rw [show π / |b| * (|b| / π) = 1 by field_simp] at h3
          replace hn : |n| < 1:= by
            rify
            simp at hn
            linarith
          have hn1 : |n| ≥ 0:= by positivity
          replace hn1 : |n| = 0:= by linarith
          simp at hn1
          subst n
          simp at h
          rcases h with h | h
          .
            linarith
          .
            subst b
            simp at g2
        -- Case where cos(ax² + c) = 0
        .
          exact h
      -- Prove that a = 0 using the lemma above
      have h3 : a = 0:= by
        by_contra H
        -- Choose specific values y and z to derive contradiction
        set y:= π / |b| * (1 / 2) with hy
        set z:= min (y / 2) (π / (4 * |a| * y)) with hz
        clear_value y z
        have g1 : π / |b| > 0:= by positivity
        -- Apply h2 to y and y+z
        have gy:= h2 y (by subst y ; positivity) (by subst y ; linarith)
        have g2 : z > 0:= by
          subst z
          have g2 : y / 2 > 0:= by subst y ; positivity
          have g3 : π / (4 * |a| * y) > 0:= by
            have g3 : y > 0:= by linarith
            positivity
          exact lt_min g2 g3
        have g3 : y + z < π / |b|:= by
          have g1 : z ≤ y / 2:= by
            subst z
            exact min_le_left (y / 2) (π / (4 * |a| * y))
          subst y
          linarith
        have gz:= h2 (y + z) (by linarith) g3
        -- Both cos values are zero, so they equal π/2 + kπ for some integers
        apply Real.cos_eq_zero_iff.1 at gy
        rcases gy with ⟨k, hk⟩
        apply Real.cos_eq_zero_iff.1 at gz
        rcases gz with ⟨m, hm⟩
        by_cases h4 : k = m
        -- If k = m, derive contradiction
        .
          subst k
          replace hk : a * (2 * y + z) * z = 0:= by linarith
          simp [H] at hk
          rcases hk with hk | hk
          all_goals
            linarith
        -- If k ≠ m, derive contradiction through size estimates
        .
          replace hk : a * (2 * y + z) * z = (m - k) * π:= by linarith
          replace hk : |a * (2 * y + z) * z| = |(m - k) * π|:= by rw [hk]
          rw [show |((↑m : ℝ) - k) * π| = |(↑m : ℝ) - k| * |π| by exact abs_mul ((↑m : ℝ) - k) π] at hk
          rw [show |a * (2 * y + z) * z| = |a * (2 * y + z)| * |z| by exact abs_mul (a * (2 * y + z)) z] at hk
          rw [show |a * (2 * y + z)| = |a| * |2 * y + z| by exact abs_mul a (2 * y + z)] at hk
          rw [show |2 * y + z| = 2 * y + z by exact abs_of_pos (by linarith)] at hk
          rw [show |z| = z by exact abs_of_pos g2] at hk
          rw [show |π| = π by exact abs_of_nonneg (by positivity)] at hk
          replace h4 : |m - k| > 0:= by
            by_contra H
            simp at H
            replace H : k = m:= by linarith
            trivial
          replace h4 : |m - k| ≥ 1:= by omega
          rify at h4
          have g4 : π ≥ 0:= by positivity
          replace h4 : |(↑m : ℝ) - k| * π ≥ π:= by exact le_mul_of_one_le_left g4 h4
          -- Show the left side is smaller than π, contradiction
          suffices |a| * (2 * y + z) * z < π by linarith
          have h5 : z * z ≤ z * y:= by
            replace g1 : z ≤ y:= by linarith
            replace g2 : z ≥ 0:= by positivity
            exact mul_le_mul_of_nonneg_left g1 g2
          have h6 : z * y ≤ π / (4 * |a|):= by
            have g5 : z ≤ π / (4 * |a| * y):= by
              subst z
              exact min_le_right (y / 2) (π / (4 * |a| * y))
            have g6 : y > 0:= by linarith
            replace H : |a| > 0:= by positivity
            rw [show π / (4 * |a|) = π / (4 * |a| * y) * y by field_simp ; linarith]
            replace g6 : y ≥ 0:= by positivity
            exact mul_le_mul_of_nonneg_right g5 g6
          replace h5 : (2 * y + z) * z ≤ 3 * y * z:= by linarith
          replace H : |a| > 0:= by positivity
          rw [show |a| * (2 * y + z) * z = |a| * ((2 * y + z) * z) by ring]
          suffices (2 * y + z) * z < π / |a| by exact (lt_div_iff₀' H).mp this
          rw [show π / (4 * |a|) = π / |a| * (1 / 4) by ring] at h6
          linarith [show π / |a| > 0 by positivity]
      -- Now that a = 0, determine the form of c
      subst a
      simp at h2
      have g1 : π / |b| > 0:= by positivity
      specialize h2 (π / |b| * (1 / 2)) (by linarith) (by linarith)
      apply Real.cos_eq_zero_iff.1 at h2
      rcases h2 with ⟨k, hk⟩
      subst c
      simp
      right
      use k
      linarith
  -- Backward direction: if b = 0 or (a = 0 and c = π/2 + kπ), then f is even
  .
    intro h
    simp at h
    rcases h with h | h
    -- Case 1: b = 0, then f(x) = sin(ax² + c) = f(-x)
    .
      subst b
      simp
    -- Case 2: a = 0 and c = π/2 + kπ, then f(x) = sin(bx + c)
    .
      rcases h with ⟨ha, hc⟩
      subst a
      simp
      intro x
      -- Show sin(bx + c) = sin(-bx + c) by using sine difference formula
      apply sub_eq_zero.1
      rw [Real.sin_sub_sin (b * x + c)  (-(b * x) + c)]
      ring_nf
      -- Since c = π/2 + kπ, we have cos(c) = 0
      replace hc : cos c = 0:= by
        apply Real.cos_eq_zero_iff.2
        rcases hc with ⟨k, hk⟩
        use k
        linarith
      rw [hc]
      simp

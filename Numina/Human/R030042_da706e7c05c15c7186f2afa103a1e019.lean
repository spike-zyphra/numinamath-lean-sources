import Mathlib
/- Suppose $x$ is a rational number such that $x \sqrt{2}$ is also rational. Find $x$. -/
theorem number_theory_609726 (x : ℚ) : (∃ r : ℚ, x * √2 = r) ↔ x = 0:= by
  -- We'll prove both directions of the iff
  constructor
  -- Forward direction: if x√2 is rational, then x = 0
  .
    intro h
    -- Proof by contradiction: assume x ≠ 0
    by_contra H
    -- Extract the rational number r such that x√2 = r
    rcases h with ⟨r, h⟩
    -- This lemma shows that if √2 equals a rational, then it equals an integer
    have h1 : (∃ t : ℚ, √2 = t) → (∃ k : ℤ, √2 = k):= by
      intro h
      rcases h with ⟨t, ht⟩
      -- Square both sides of √2 = t
      have h1 : √2 ^ 2 = t ^ 2:= by rw [ht]
      field_simp at h1
      -- Establish that t² = 2
      replace h2 : t ^ 2 = 2:= by rify ; linarith
      -- Show that the denominator of t² equals the denominator of 2 (which is 1)
      replace h2 : (t ^ 2).den = (2 : ℚ).den:= by rw [←h2]
      norm_num at h2
      -- Conclude that t's denominator must be 1
      replace h2 : t.den = 1:= by exact Nat.eq_one_of_mul_eq_one_left h2
      -- Rewrite t as its numerator divided by its denominator
      rw [show t = t.num / t.den by field_simp] at ht
      rw [h2] at ht
      simp at ht
      -- Therefore √2 equals an integer (t.num)
      use t.num
    -- Apply the lemma to show that √2 = r/x is an integer k
    replace h1:= h1 (by use r / x ; field_simp ; linarith)
    rcases h1 with ⟨k, hk⟩
    -- Establish that k is positive
    have hkpos : k > 0:= by
      rify
      rw [←hk]
      positivity
    -- Square both sides of √2 = k
    replace hk : √2 ^ 2 = k ^ 2:= by rw [hk]
    field_simp at hk
    -- Establish that 2 = k²
    replace hk : 2 = k ^ 2:= by rify ; linarith
    -- Prove that k > 1
    have hk1 : k > 1:= by
      by_contra H
      simp at H
      replace H : k ^ 2 ≤ 1:= by nlinarith only [H, hkpos]
      linarith
    -- Prove that k < 2
    have hk2 : k < 2:= by
      by_contra H
      simp at H
      replace H : k ^ 2 ≥ 4:= by nlinarith only [H]
      linarith
    -- Reach a contradiction: we've shown 1 < k < 2, but no integer satisfies this
    linarith
  -- Reverse direction: if x = 0, then x√2 is rational
  .
    intro hx
    -- The rational number is 0
    use 0
    subst x
    simp

import Mathlib
/- Let $a_{1}, a_{2}, a_{3}, \cdots$ be a family of strictly positive real numbers such that for any non-zero natural number $k$ we have:

$$
a_{k+1} \geqslant \frac{k a_{k}}{a_{k}^{2}+(k-1)}
$$

Show that for all integers $k \geqslant 2$, we have:

$$
a_{1}+a_{2}+\cdots+a_{k} \geqslant k
$$ -/
theorem number_theory_162753 (a : ℕ → ℝ) (hpos : ∀ k : ℕ, a k > 0) (h : ∀ k : ℕ, a (k + 1) ≥ (k + 1) * a k / (a k ^ 2 + k)) : ∀ n : ℕ, ∑ i in Finset.range (n + 2), a i ≥ n + 2:= by
  intro n
  induction n with
  -- Base case: n = 0, proving that a₀ + a₁ ≥ 2
  | zero =>
    simp [Finset.sum_range_succ]
    specialize h 0
    simp at h
    have g1:= hpos 0
    -- Rewrite the inequality to a simpler form
    rw [show a 0 / a 0 ^ 2 = 1 / a 0 by field_simp ; ring_nf] at h
    -- Reformulate what we need to prove
    suffices a 0 + 1 / a 0 - 2 ≥ 0 by linarith
    -- Use AM-GM inequality: a₀ + 1/a₀ ≥ 2 for a₀ > 0
    rw [show a 0 + 1 / a 0 - 2 = (a 0 - 1) ^ 2 / a 0 by field_simp ; ring_nf]
    positivity
  -- Inductive step: assuming the result for n, prove it for n+1
  | succ n ih =>
    -- Lemma: For any k, the sum of first k terms is at least k/a_k
    have h1 : ∀ k : ℕ, ∑ i in Finset.range k, a i ≥ k / a k:= by
      intro k
      induction k with
      -- Base case for the lemma: k = 0
      | zero =>
        simp
      -- Inductive step for the lemma
      | succ k ih =>
        rw [Finset.sum_range_succ]
        simp at ih ⊢
        specialize h k
        have g1:= hpos k
        -- Establish that the denominator is positive
        have g3 : a k ^ 2 + ↑k > 0:= by positivity
        -- Manipulate the recurrence relation
        replace h : a (k + 1) * (a k ^ 2 + ↑k) ≥ (↑k + 1) * a k:= by exact (mul_inv_le_iff₀ g3).mp h
        replace h : a k ^ 2 + ↑k ≥ (↑k + 1) * a k / a (k + 1):= by exact (div_le_iff₀' (hpos (k + 1))).mpr h
        rw [show (↑k + 1) * a k / a (k + 1) = (↑k + 1) / a (k + 1) * a k by ring] at h
        replace h : (a k ^ 2 + k) / a k ≥ (↑k + 1) / a (k + 1):= by exact (le_div_iff₀ (hpos k)).mpr h
        -- Simplify the expression
        rw [show (a k ^ 2 + k) / a k = a k + k / a k by field_simp ; ring_nf] at h
        linarith
    simp
    -- Rewrite n+1+2 as n+2+1 for clarity
    rw [show n + 1 + 2 = n + 2 + 1 by ring]
    rw [Finset.sum_range_succ]
    simp at ih
    -- Apply the lemma to n+2
    specialize h1 (n + 2)
    -- Define x as the sum of the first n+2 terms for cleaner notation
    set x:= ∑ i in Finset.range (n + 2), a i with hx
    clear_value x
    simp at h1
    -- Manipulate the inequality from the lemma
    replace h1 : n + 2 ≤ x * a (n + 2):= by exact (mul_inv_le_iff₀ (hpos (n + 2))).mp h1
    have g1 : x > 0:= by linarith
    replace h1 : a (n + 2) ≥ (n + 2) / x:= by exact (div_le_iff₀' g1).mpr h1
    -- Use AM-GM inequality: x + (n+2)/x ≥ 2√(n+2) ≥ n+3 for x ≥ n+2
    suffices x + (n + 2) / x - (n + 3) ≥ 0 by linarith
    rw [show x + (n + 2) / x - (n + 3) = (x - 1) * (x - (n + 2)) / x by field_simp ; ring_nf]
    -- Use the induction hypothesis to show x ≥ n+2
    replace ih : x - (n + 2) ≥ 0:= by linarith
    have g2 : x - 1 > 0:= by linarith
    positivity

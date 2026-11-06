import Mathlib
/- Let $\mathbb{R}^{+}$be the set of all positive real numbers. Find all functions $f: \mathbb{R}^{+} \rightarrow \mathbb{R}^{+}$such that

$$
\frac{f(a)}{1+a+c a}+\frac{f(b)}{1+b+a b}+\frac{f(c)}{1+c+b c}=1
$$

for all $a, b, c \in \mathbb{R}^{+}$that satisfy $a b c=1$.
Answer: $f(x)=k x+1-k$ where $k$ is any real number such that $0 \leq k \leq 1$. -/
theorem algebra_605068 (f : ℝ → ℝ) (hf : ∀ x > 0, f x > 0) : (∀ a b c : ℝ, a > 0 → b > 0 → c > 0 → a * b * c = 1 →
f a / (1 + a + c * a) + f b / (1 + b + a * b) + f c / (1 + c + b * c) = 1)
↔ (∃ k : ℝ, 0 ≤ k ∧ k ≤ 1 ∧ ∀ x > 0, f x = k * x + 1 - k):= by
  constructor
  .
    intro h
    -- First key lemma: Reformulates the functional equation in a more manageable form
    have h1 : ∀ b c : ℝ, b > 0 → c > 0 → b * c * f (1 / (b * c)) + c * f b + f c = 1 + c + b * c:= by
      intro b c hb hc
      specialize h (1 / (b * c)) b c (by positivity) hb hc (by field_simp)
      field_simp at h
      replace h : ((b * c + 1 + c) * ((1 + b) * (b * c) + b)) * (b * c * f (1 / (b * c)) + c * f b + f c - (1 + c + b * c)) = 0:= by linarith
      have g1 : (b * c + 1 + c) * ((1 + b) * (b * c) + b) ≠ 0:= by positivity
      simp [g1] at h
      simp
      linarith

    -- Proves that f(1) = 1, a crucial property
    have h2 : f 1 = 1:= by
      specialize h1 1 1 (by linarith) (by linarith)
      simp at h1
      linarith

    -- Key functional equation: Relates f(b), f(c), and f(bc)
    have h3 : ∀ b c : ℝ, b > 0 → c > 0 → c * f b + f c = c + f (b * c):= by
      intro b c hb hc
      have g1:= h1 (b * c) 1 (by positivity) (by positivity)
      specialize h1 b c hb hc
      simp at g1 h1
      linarith

    -- Shows f must be of the form f(x) = kx + (1-k)
    have h4 : ∀ b : ℝ, b > 0 → f b = b * (f 2 - 1) + 1 - (f 2 - 1):= by
      intro b hb
      have g1:= h3 b 2 hb (by linarith)
      have g2:= h3 2 b (by linarith) (by linarith)
      ring_nf at g1 g2
      linarith

    -- Defines k = f(2) - 1 and proves 0 ≤ k ≤ 1
    set k:= f 2 - 1 with hk
    clear_value k
    -- Proves k ≥ 0
    have hk1 : k ≥ 0:= by
      by_contra H
      simp at H
      replace H : -k > 0:= by linarith
      specialize h4 ((1 + -k) / -k) (by positivity)
      specialize hf ((1 + -k) / -k) (by positivity)
      rw [h4] at hf
      field_simp at hf
      ring_nf at hf
      simp at hf

    -- Case analysis on whether k = 0
    by_cases hk3 : k = 0
    .
      subst k
      use 0
      simp
      intro x hx
      specialize h4 x hx
      rw [hk3] at h4
      simp at h4
      exact h4
    .
      replace hk1 : k > 0:= by positivity
      clear hk3
      -- Proves k ≤ 1
      have hk2 : k ≤ 1:= by
        by_contra H
        simp at H
        replace H : k - 1 > 0:= by linarith
        specialize h4 ((k - 1) / (2 * k)) (by positivity)
        specialize hf ((k - 1) / (2 * k)) (by positivity)
        rw [h4] at hf
        field_simp at hf
        ring_nf at hf
        replace hf : k * (1 - k) > 0:= by linarith
        replace hf : 1 - k > 0:= by exact (pos_iff_pos_of_mul_pos hf).mp hk1
        linarith
      use k
      refine ⟨?_, ?_, ?_⟩
      .
        linarith
      .
        exact hk2
      .
        intro x hx
        specialize h4 x hx
        linarith
  .
    -- Proves the reverse direction: any function of the form f(x) = kx + (1-k) satisfies the equation
    intro h
    rcases h with ⟨k, _, _, h⟩
    intro a b c ha hb hc habc
    rw [h a ha, h b hb, h c hc]
    field_simp
    replace habc : a = 1 / (b * c):= by
      field_simp
      linarith
    subst a
    field_simp
    ring_nf

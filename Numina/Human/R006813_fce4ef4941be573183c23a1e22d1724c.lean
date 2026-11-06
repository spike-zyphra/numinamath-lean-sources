import Mathlib
/- Let $N$ be a positive integer that is not a perfect square. Let $a, b$ and $c$ be positive integers such that $\frac{a \sqrt{N}+b}{b \sqrt{N}+c}$ is a rational number. Show that $\frac{a^{2}+b^{2}+c^{2}}{a+b+c}$ and $\frac{a^{3}-2 b^{3}+c^{3}}{a+b+c}$ are both integers. -/
lemma sqrt_not_rat : ∀ a : ℕ, (∃ r : ℚ, √a = r) → ∃ t : ℕ, √a = t:= by
    intro a h
    rcases h with ⟨r, hr⟩
    have h2:= Rat.mul_self_den r
    have h:= hr
    replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
    field_simp at hr
    replace hr : a = r ^ 2:= by rify ; linarith
    have g2 : (↑a : ℚ).den = 1:= by exact rfl
    rw [show r * r = r ^ 2 by ring_nf] at h2
    rw [hr, h2] at g2
    simp at g2
    rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
    rw [g2] at h
    simp at h
    use (r.num).natAbs
    rw [show (↑(r.num).natAbs : ℝ) = (↑(r.num).natAbs : ℤ) by exact rfl]
    simp
    rw [h]
    rw [abs_of_nonneg (by rw [←h] ; positivity)]
theorem number_theory_641408 (a b c n : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (h : ∃ r : ℚ, (a * √n + b) / (b * √n + c) = r) (hn : ¬IsSquare n): (∃ k : ℤ, (a ^ 2 + b ^ 2 + c ^ 2) / ((↑a : ℝ) + b + c) = k) ∧ (∃ k : ℤ, (a ^ 3 - 2 * b ^ 3 + c ^ 3) / ((↑a : ℝ) + b + c) = k):= by
    -- First, we prove that b² = ac using the rationality condition
    replace h : b ^ 2 = a * c:= by
      rcases h with ⟨r, h⟩
      -- Prove that n > 0 by contradiction
      have h1 : n > 0:= by
        by_contra H
        simp at H
        subst n
        absurd hn
        simp
      -- Algebraic manipulation to show b² = ac
      field_simp at h
      replace h : (↑a * √↑n + ↑b) * (b * √n - c) = ↑r * (↑b * √↑n + ↑c) * (b * √n - c):= by rw [h]
      ring_nf at h
      field_simp at h
      replace h : (b ^ 2 - a * c) * √n = ↑n * ↑b ^ 2 * ↑r - ↑c ^ 2 * ↑r + b * c - a * b * n:= by linarith
      rify
      suffices (b : ℝ) ^ 2 - a * c = 0 by linarith
      by_contra H
      replace h : ∃ r : ℚ, √n = r:= by
        use (↑n * ↑b ^ 2 * ↑r - ↑c ^ 2 * ↑r + b * c - a * b * n) / (b ^ 2 - a * c)
        simp
        field_simp
        linarith
      replace h:= sqrt_not_rat n h
      rcases h with ⟨t, h⟩
      replace h : √n ^ 2 = t ^ 2:= by rw [h]
      field_simp at h
      replace h : n = t ^ 2:= by
        rify
        linarith
      absurd hn
      subst n
      use t
      ring

    -- Convert the equation to real numbers for calculation
    rify at h
    -- Express a in terms of b and c: a = b²/c
    replace h : (a : ℝ) = b ^ 2 / c:= by
      field_simp
      linarith

    -- Prove both parts of the conjunction
    constructor
    -- First part: Show that (a² + b² + c²)/(a + b + c) = (a - b + c)
    .
      use (a - b + c)
      field_simp
      rw [h]
      field_simp
      ring_nf
    -- Second part: Show that (a³ - 2b³ + c³)/(a + b + c) = (a + c - 2b)(a + b + c)
    .
      use (a + c - 2 * b) * (a + b + c)
      field_simp
      rw [h]
      field_simp
      ring_nf

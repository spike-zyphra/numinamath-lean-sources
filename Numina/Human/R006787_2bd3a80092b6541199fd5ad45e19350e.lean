import Mathlib
/- Let $K$ be a non-zero natural number. Let $a, b, c$ be natural numbers such that $a \neq 0, b \neq 0$ and $c = a + \frac{b}{K^2 a} - \frac{1}{b}$. Prove that $c$ is a square of some natural number. -/
theorem number_theory_641149 (a b c k : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hk : k ≠ 0) (h1 : (↑c : ℝ) = a + b / (k ^ 2 * a) - 1 / b) : IsSquare c:= by
  -- Simplify the equation by clearing denominators
  field_simp at h1
  -- Rearrange the equation to isolate terms
  replace h1 : k ^ 2 * a * b * ((↑c : ℝ) - a) = b ^ 2 - ↑k ^ 2 * ↑a:= by linarith
  -- Show that k²ab divides b² - k²a
  have h2 : (↑k : ℤ) ^ 2 * a * b ∣ (↑b : ℤ) ^ 2 - k ^ 2 * a:= by
    use c - a
    rify
    linarith
  -- Extract the quotient d from the divisibility relation
  rcases h2 with ⟨d, h2⟩
  rify at h2
  rw [h2] at h1
  -- Simplify the equation using the divisibility relation
  replace h1 : k ^ 2 * a * b * (d - (c - (↑a : ℝ))) = 0:= by linarith
  simp [ha, hb, hk] at h1
  -- Rewrite the divisibility relation in terms of d
  replace h2 : ↑b ^ 2 - ↑k ^ 2 * ↑a = (↑k : ℤ) ^ 2 * ↑a * ↑b * ↑d:= by
    rify
    linarith
  -- Prove that d is non-negative
  have hdpos : d ≥ 0:= by
    replace h2 : b ^ 2 = k ^ 2 * a * (1 + b * d):= by linarith
    by_contra H
    simp at H
    replace hb : b > 0:= by omega
    replace H : d * b < 0:= by
      zify at hb
      exact Int.mul_neg_of_neg_of_pos H hb
    have g : k ^ 2 * a ≥ 0:= by positivity
    replace H : 1 + b * d ≤ 0:= by linarith
    have g1 : b ^ 2 > 0:= by positivity
    have g2 : b ^ 2 ≤ 0:= by
      zify
      rw [h2]
      zify at g
      exact Int.mul_nonpos_of_nonneg_of_nonpos g H
    linarith
  -- Rearrange the equation to get a perfect square form
  replace h2 : k ^ 2 * a * (d ^ 2 * k ^ 2 * a + 4) = (2 * b - d * k ^ 2 * a) ^ 2:= by linarith
  -- Define t as the absolute value of the right side
  set t:= |2 * b - d * k ^ 2 * a| with ht
  clear_value t
  rw [show (2 * b - d * k ^ 2 * a) ^ 2 = t ^ 2 by subst t ; exact Eq.symm (sq_abs (2 * ↑b - d * ↑k ^ 2 * ↑a))] at h2
  -- Show that k² divides t²
  have h3 : (↑k : ℤ) ^ 2 ∣ t ^ 2:= by
    use a * (d ^ 2 * k ^ 2 * a + 4)
    linarith
  -- Convert to natural numbers and show k² divides (natAbs t)²
  replace h3 : k ^ 2 ∣ (t.natAbs) ^ 2:= by
    zify
    replace ht : t ≥ 0:= by
      subst t
      positivity
    rw [abs_of_nonneg ht]
    exact h3
  -- Use the fact that if k² divides a square, then k divides the base
  replace h3 : k ∣ t.natAbs:= by
    have g1 : 2 ≠ 0:= by omega
    exact (Nat.pow_dvd_pow_iff g1).mp h3
  zify at h3
  rw [abs_of_nonneg (show t ≥ 0 by subst t ; positivity)] at h3
  -- Extract x such that t = kx
  rcases h3 with ⟨x, hx⟩
  clear ht
  subst t
  -- Simplify the equation using the relation t = kx
  replace h2 : k ^ 2 * (a * (d ^ 2 * k ^ 2 * a + 4) - x ^ 2) = 0:= by linarith
  simp [hk] at h2
  rw [show x ^ 2 = |x| ^ 2 by exact Eq.symm (sq_abs x)] at h2
  -- Factor the equation as a difference of squares
  replace h2 : (|x| + d * k * a) * (|x| - d * k * a) = 4 * a:= by linarith
  -- Prove that |x| + dka is even
  have h3 : Even (|x| + d * k * a):= by
    by_contra H
    simp at H
    have h4 : Odd (|x| - d * k * a):= by
      rw [show |x| - d * k * a = |x| + d * k * a + 2 * (-d * k * a) by ring]
      have h5 : Even (2 * (-d * k * a)):= by
        use -d * k * a
        ring
      exact Even.odd_add h5 H
    replace H : Odd (4 * (↑a : ℤ)):= by
      rw [←h2]
      exact Odd.mul H h4
    absurd H
    simp
    use 2 * a
    ring
  -- Prove that |x| - dka is also even
  have h4 : Even (|x| - d * k * a):= by
    rw [show |x| - d * k * a = |x| + d * k * a + 2 * (-d * k * a) by ring]
    have h5 : Even (2 * (-d * k * a)):= by
      use -d * k * a
      ring
    exact Even.add h3 h5
  -- Extract v and u such that |x| + dka = 2v and |x| - dka = 2u
  rcases h3 with ⟨v, hv⟩
  rcases h4 with ⟨u, hu⟩
  rw [hv, hu] at h2
  ring_nf at h2
  -- Show that v * u = a
  replace h2 : v * u = a:= by linarith
  -- Show that v - u = dka
  have h3 : v - u = d * k * a:= by linarith
  -- Case analysis on whether d = 0
  by_cases hd : d = 0
  .
    -- Case 1: d = 0
    subst d
    ring_nf at hu hv
    simp at h1
    -- Show that c = a when d = 0
    replace h1 : c = a:= by
      rify
      linarith
    subst c
    -- Show that a is a perfect square
    replace h2 : 4 * a = |x| ^ 2:= by
      replace h2 : (u * 2) * (v * 2) = 4 * a:= by linarith
      rw [←hu, ←hv] at h2
      linarith
    rw [hu] at h2
    replace h2 : a = u ^ 2:= by linarith
    use u.natAbs
    zify
    ring_nf
    rw [h2]
    exact Eq.symm (sq_abs u)
  .
    -- Case 2: d ≠ 0
    ring_nf at hv hu
    -- Show that v > 0
    have hvpos : v > 0:= by
      suffices v * 2 > 0 by linarith
      rw [←hv]
      positivity
    -- Show that u > 0
    have hupos : u > 0:= by
      suffices v * u > 0 by exact (pos_iff_pos_of_mul_pos this).mp hvpos
      rw [h2]
      positivity
    -- Show that v ≥ a + 1
    replace h3 : v ≥ a + 1:= by
      have g1 : d * k > 0:= by positivity
      replace g1 : d * k ≥ 1:= by omega
      have g2 : (↑a : ℤ) ≥ 0:= by positivity
      replace g1 : d * k * a ≥ a:= by exact le_mul_of_one_le_left g2 g1
      linarith
    replace hupos : u ≥ 1:= by linarith
    -- Show that v * u ≥ (a + 1) * 1, which contradicts v * u = a
    replace h3 : v * u ≥ (a + 1) * 1:= by refine Int.mul_le_mul h3 hupos (by linarith) (by linarith)
    linarith

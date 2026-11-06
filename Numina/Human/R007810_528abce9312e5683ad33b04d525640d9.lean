import Mathlib
/- Soit $a, b, c, d$ des réels strictement positifs tels que : $a+b+c+d=1$. Montrer que :

$$
\frac{a^{4}}{a^{3}+a^{2} b+a b^{2}+b^{3}}+\frac{b^{4}}{b^{3}+b^{2} c+b c^{2}+c^{3}}+\frac{c^{4}}{c^{3}+c^{2} d+c d^{2}+d^{3}}+\frac{d^{4}}{d^{3}+d^{2} a+d a^{2}+a^{3}} \geqslant \frac{1}{4}
$$

et déterminer les cas d'égalité. -/
theorem algebra_607256 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + b + c + d = 1) :
    1 / 4 ≤ a ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
    b ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) +
    c ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) +
    d ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3) ∧
    (1 / 4 = a ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
    b ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) +
    c ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) +
    d ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3) ↔
      (a = 1 / 4 ∧ b = 1 / 4 ∧ c = 1 / 4 ∧ d = 1 / 4)) := by

        -- Prove that cyclic permutation of terms doesn't change the sum
        have h1 : a ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
    b ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) +
    c ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) +
    d ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3) = b ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) +
    c ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) +
    d ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) +
    a ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3):= by

          -- Prove difference of adjacent terms equals difference of variables
          have h1 : a ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) - b ^ 4 / (a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3) = a - b:= by
            field_simp
            linarith
          have h2 : b ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) - c ^ 4 / (b ^ 3 + b ^ 2 * c + b * c ^ 2 + c ^ 3) = b - c:= by
            field_simp
            linarith
          have h3 : c ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) - d ^ 4 / (c ^ 3 + c ^ 2 * d + c * d ^ 2 + d ^ 3) = c - d:= by
            field_simp
            linarith
          have h4 : d ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3) - a ^ 4 / (d ^ 3 + d ^ 2 * a + d * a ^ 2 + a ^ 3) = d - a:= by
            field_simp
            linarith
          linarith

        -- Key lemma: For any two positive reals x,y, proves inequality and characterizes equality case
        have h2 : ∀ x y : ℝ, x > 0 → y > 0 → x ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) + y ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) ≥ (x + y) / 4 ∧ (x ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) + y ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) = (x + y) / 4 → x = y):= by
          intro x y hx hy
          rw [show x ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) + y ^ 4 / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) = (x ^ 4 + y ^ 4) / (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) by ring]
          rw [show x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 = (x + y) * (x ^ 2 + y ^ 2) by ring]
          have g1 : (x + y) * (x ^ 2 + y ^ 2) > 0:= by positivity
          constructor
          .
            suffices x ^ 4 + y ^ 4 ≥ (x + y) / 4 * ((x + y) * (x ^ 2 + y ^ 2)) by exact (le_div_iff₀ g1).mpr this
            have g2 : x ^ 4 + y ^ 4 ≥ (x ^ 2 + y ^ 2) ^ 2 / 2:= by
              have g2 : (x ^ 2 - y ^ 2) ^ 2 ≥ 0:= by positivity
              linarith
            have g3 : (x - y) ^ 2 * (x ^ 2 + y ^ 2) ≥ 0:= by positivity
            linarith
          .
            intro h
            field_simp at h
            have g2 : (x ^ 2 - y ^ 2) ^ 2 ≥ 0:= by positivity
            have g3 : (x ^ 2 + y ^ 2) * (x - y) ^ 2 ≥ 0:= by positivity
            replace g2 : (x ^ 2 - y ^ 2) ^ 2 = 0:= by linarith
            replace g2 : x ^ 2 - y ^ 2 = 0:= by exact pow_eq_zero g2
            replace g2 : (x + y) * (x - y) = 0:= by linarith
            replace g3 : x + y ≠ 0:= by positivity
            replace g2 : x - y = 0:= by exact eq_zero_of_ne_zero_of_mul_left_eq_zero g3 g2
            linarith

        -- Apply the key lemma to each adjacent pair
        have h3:= h2 a b ha hb
        have h4:= h2 b c hb hc
        have h5:= h2 c d hc hd
        have h6:= h2 d a hd ha
        rcases h3 with ⟨h3, h3eq⟩
        rcases h4 with ⟨h4, h4eq⟩
        rcases h5 with ⟨h5, h5eq⟩
        rcases h6 with ⟨h6, h6eq⟩
        constructor
        .
          clear h2 h3eq h4eq h5eq h6eq
          linarith
        .
          constructor
          .
            intro hgoal
            replace h3eq:= h3eq (by linarith)
            replace h4eq:= h4eq (by linarith)
            replace h5eq:= h5eq (by linarith)
            clear h1 h2 h3 h4 h5 h6 h6eq hgoal
            refine ⟨?_, ?_, ?_, ?_⟩
            all_goals
            linarith
          .
            intro hgoal
            rcases hgoal with ⟨hgoal1, hgoal2, hgoal3, hgoal4⟩
            subst a b c d
            ring_nf

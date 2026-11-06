import Mathlib
/- Find the minimum possible value of  $$ \frac{a}{b^{3}+4}+\frac{b}{c^{3}+4}+\frac{c}{d^{3}+4}+\frac{d}{a^{3}+4} $$  given that $a, b, c, d$ are nonnegative real numbers such that $a+b+c+d=4$. -/
theorem algebra_605465 :
  IsLeast {x : ℝ | ∃ a b c d : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ d ≥ 0 ∧ a + b + c + d = 4 ∧ x =
    a / (b ^ 3 + 4) + b / (c ^ 3 + 4) + c / (d ^ 3 + 4) + d / (a ^ 3 + 4)} (2 / 3) := by
      constructor
      -- Part 1: Prove that 2/3 belongs to the set by providing a specific example
      .
        simp
        -- Let a = 2
        use 2
        simp
        -- Let b = 2
        use 2
        simp
        -- Let c = 0
        use 0
        simp
        -- Let d = 0
        use 0
        simp
        constructor
        all_goals
        ring_nf
      -- Part 2: Prove that 2/3 is indeed the minimum value
      .
        simp [lowerBounds]
        intro x a ha b hb c hc d hd h hx
        subst x
        -- Key inequality: For any x,y ≥ 0, x/(y³+4) ≥ x(1/4 - y/12)
        have h1 : ∀ x y : ℝ, x ≥ 0 → y ≥ 0 → x / (y ^ 3 + 4) ≥ x * (1 / 4 - y / 12):= by
          intro x y hx hy
          rw [show x / (y ^ 3 + 4) = x * (1 / (y ^ 3 + 4)) by ring]
          -- Prove that 1/(y³+4) ≥ 1/4 - y/12
          have h1 : 1 / (y ^ 3 + 4) ≥ 1 / 4 - y / 12:= by
            have h1 : y ^ 3 + 4 > 0:= by positivity
            suffices (y ^ 3 + 4) * (1 / (y ^ 3 + 4)) ≥ (y ^ 3 + 4) * (1 / 4 - y / 12) by exact le_of_mul_le_mul_left this h1
            rw [show (y ^ 3 + 4) * (1 / (y ^ 3 + 4)) = 1 by field_simp]
            -- Use the fact that y(y+1)(y-2)² ≥ 0 for y ≥ 0
            replace h1 : y * (y + 1) * (y - 2) ^ 2 ≥ 0:= by positivity
            linarith
          exact mul_le_mul_of_nonneg_left h1 hx
        -- Apply the inequality to each term
        have h2:= h1 a b ha hb
        have h3:= h1 b c hb hc
        have h4:= h1 c d hc hd
        have h5:= h1 d a hd ha
        suffices a * (1 / 4 - b / 12) + b * (1 / 4 - c / 12) + c * (1 / 4 - d / 12) + d * (1 / 4 - a / 12) ≥ 2 / 3 by linarith
        clear h1 h2 h3 h4 h5
        -- Final step: Use the fact that ab + bc + cd + da ≤ 4 when a+b+c+d=4
        have h1 : a * b + b * c + c * d + d * a ≤ 4:= by
          have h1 : ((a + b + c + d) / 2) ^ 2 = 4:= by rw [h] ; ring_nf
          rw [←h1]
          replace h1 : (a + c - b - d) ^ 2 ≥ 0:= by positivity
          linarith
        linarith

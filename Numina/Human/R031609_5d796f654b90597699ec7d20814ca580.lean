import Mathlib

/- Find the largest positive integer $n$ for which the inequality

$$
\frac{a+b+c}{a b c+1}+\sqrt[n]{a b c} \leq \frac{5}{2}
$$

holds for all $a, b, c \in[0,1]$. Here $\sqrt[1]{a b c}=a b c$. -/
theorem inequalities_604480 :
    IsGreatest {n : ℕ | n > 0 ∧ ∀ a b c : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 → (a + b + c) / (a * b * c + 1) + (a * b * c) ^ (1 / n : ℝ) ≤ 5 / 2} 3 := by
  -- Break the goal into two parts.
  simp [IsGreatest, upperBounds, -one_div]
  refine ⟨?_, ?_⟩
  . -- First show that n = 3 works.
    intro a b c ha₀ ha₁ hb₀ hb₁ hc₀ hc₁
    -- Prove that a + b + c ≤ abc + 2.
    have h₀ : a + b + c ≤ a * b * c + 2 := by
      -- This is equivalent to (1 - a)(1 - b) + (1 - ab)(1 - c) ≥ 0.
      nlinarith only [ha₁, hb₁, hc₁, show a * b ≤ 1 by nlinarith]
    -- Let y = (abc) ^ (1 / 3).
    let y := (a * b * c) ^ (1 / 3 : ℝ)
    -- Prove that y ≤ 1.
    have h₁ : y ≤ 1 ^ (1 / 3 : ℝ) := by
      -- This is equivalent to abc ≤ 1.
      rw [Real.rpow_le_rpow_iff (by positivity) (by norm_num) (by norm_num), show (1 : ℝ) = 1 * 1 * 1 by norm_num]
      apply mul_le_mul
      apply mul_le_mul
      all_goals
        first | assumption | norm_num
    simp at h₁
    -- Show that 1 / (y³ + 1) + y ≤ 3 / 2.
    have h₂ : 1 / (y ^ 3 + 1) + y ≤ 3 / 2 := by
      -- Simplify the expression.
      field_simp
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      -- This is equivalent to (1 - y)(y³ + (1 - y)²(1 + y)) ≥ 0.
      nlinarith only [h₁, show 0 ≤ y ^ 3 + (1 - y) ^ 2 * (1 + y) by positivity]
    -- Show that the inequality holds.
    calc
      (a + b + c) / (a * b * c + 1) + (a * b * c) ^ (1 / 3 : ℝ)
      ≤ (a * b * c + 2) / (a * b * c + 1) + (a * b * c) ^ (1 / 3 : ℝ) := by
        -- Apply the inequality proved before.
        apply add_le_add
        . rw [div_le_div_iff₀ (by positivity) (by positivity)]
          apply mul_le_mul h₀ (by rfl) (by positivity) (by positivity)
        . rfl
      _ = (y ^ 3 + 2) / (y ^ 3 + 1) + y := by
        -- Simplify the expression by substituting y.
        simp only [y]
        rw [<-Real.rpow_natCast, <-Real.rpow_mul]
        norm_num
        positivity
      _ ≤ 5 / 2 := by
        -- Use the inequality h₂ just proved.
        rw [show y ^ 3 + 2 = (y ^ 3 + 1) + 1 by ring, add_div, add_assoc, div_self (by positivity)]
        linarith only [h₂]
  . -- Show that n ≥ 4 does not work.
    intro n hn₀
    contrapose!
    intro hn₁
    -- Let x = 9 / 10.
    let x : ℝ := 9 / 10
    -- Show that 1 / (xⁿ + 1) + x > 3 / 2.
    have hx : 1 / (x ^ n + 1) + x > 3 / 2 := by
      calc
        1 / (x ^ n + 1) + x ≥ 1 / (x ^ 4 + 1) + x := by
          -- The case for n is as least easier than the case for 4.
          apply add_le_add
          . rw [div_le_div_iff₀ (by positivity) (by positivity), mul_le_mul_left (by norm_num)]
            apply add_le_add
            . apply pow_le_pow_of_le_one
              norm_num
              norm_num
              omega
            . rfl
          . rfl
        _ > 3 / 2 := by
          -- Simple calculation.
          norm_num [x]
    -- Let (a, b, c) = (1, 1, xⁿ).
    use 1, 1, x ^ n
    -- Show that x ^ n ≤ 1.
    have h₀ : x ^ n ≤ 1 ^ n := by
      -- This is due to x ≤ 1.
      apply pow_le_pow_left₀
      norm_num
      norm_num
    simp at h₀
    simp [show 0 ≤ x ^ n by positivity, h₀, -one_div]
    -- Use the hypothesis hx to conclude the goal.
    nth_rewrite 3 [<-Real.rpow_natCast]
    rw [<-Real.rpow_mul (by norm_num), mul_one_div_cancel (by positivity), Real.rpow_one, add_comm _ (x ^ n), <-add_assoc, add_div, div_self (by positivity)]
    linarith only [hx]

    

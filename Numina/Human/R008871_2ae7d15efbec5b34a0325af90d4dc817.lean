import Mathlib

open Real

/- Let $a, b, c$ be real numbers such that $0 \leq a \leq b \leq c$. Prove that if

$$
a+b+c=a b+b c+c a>0,
$$

then $\sqrt{b c}(a+1) \geq 2$. When does the equality hold? -/
theorem inequalities_605843 (a b c : ℝ) (h₀ : 0 ≤ a) (h₁ : a ≤ b) (h₂ : b ≤ c)
    (h₃ : a + b + c = a * b + b * c + c * a) (h₄ : 0 < a + b + c) :
    sqrt (b * c) * (a + 1) ≥ 2 ∧ (sqrt (b * c) * (a + 1) = 2 ↔ (a = 1 ∧ b = 1 ∧ c = 1 ∨ a = 0 ∧ b = 2 ∧ c = 2)) := by
  -- Note that (a + b + c)² ≥ 3(ab + bc + ca).
  have h₅ : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
    -- This is equivalent to (a - b)² + (b - c)² + (c - a)² ≥ 0.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  -- Substitute ab + bc + ca = a + b + c into the inequality.
  rw [<-h₃] at h₅
  -- Show that a + b + c ≥ 3 because a + b + c > 0.
  have {k : ℝ} : 0 < k → k ^ 2 ≥ 3 * k → k ≥ 3 := by
    intros h h'
    nlinarith
  replace h₅ := this h₄ h₅
  clear this
  -- Show that bc ≥ 1 by bc ≥ ca ≥ ab.
  have h₆ : 3 * (b * c) ≥ 3 * 1 := by
    calc
      3 * (b * c) = b * c + b * c + b * c := by ring
      _ ≥ b * c + c * a + a * b := by nlinarith
      _ ≥ 3 * 1 := by linarith
  rw [ge_iff_le, mul_le_mul_left (by norm_num)] at h₆
  have : b + c - 2 * sqrt (b * c) = (sqrt b - sqrt c) ^ 2 := by
    rw [sub_sq, sqrt_mul (by linarith), sq_sqrt (by linarith), sq_sqrt (by linarith)]
    ring
  -- We have b + c ≥ 2.
  have h₇ : b + c ≥ 2 := by
    -- Show that b + c ≥ 2, which is classical.
    calc
      b + c ≥ 2 * sqrt (b * c) := by
        linarith only [sq_nonneg (sqrt b - sqrt c), this]
      _ ≥ 2 * 1 := by
        rw [ge_iff_le, mul_le_mul_left (by norm_num)]
        simp [h₆]
      _ = 2 := by
        norm_num
  -- The constraint gives us a = (b + c - bc) / (b + c - 1) ≥ √(bc)(2-√(bc))/(2√(bc)-1)
  have h₈ : a ≥ (sqrt (b * c) * (2 - sqrt (b * c))) / (2 * sqrt (b * c) - 1) := by
    calc
      a = (b + c - b * c) / (b + c - 1) := by
        -- Use the fact that b + c - 1 ≥ 1 > 0 and a + b + c = ab + bc + ca. 
        field_simp [show b + c - 1 ≠ 0 by linarith only [h₇]]
        linarith
      _ = 1 - (b * c - 1) / (b + c - 1) := by
        field_simp [show b + c - 1 ≠ 0 by linarith only [h₇]]
      _ ≥ 1 - (b * c - 1) / (2 * sqrt (b * c) - 1) := by
        -- Use the fact that b + c ≥ 2√(bc).
        apply sub_le_sub_left
        apply div_le_div_of_nonneg_left (by linarith only [h₆]) (by linarith [show 1 ≤ sqrt (b * c) by simp [h₆]]) (by linarith [sq_nonneg (sqrt b - sqrt c)])
      _ = (sqrt (b * c) * (2 - sqrt (b * c))) / (2 * sqrt (b * c) - 1) := by
        field_simp [show 2 * sqrt (b * c) - 1 ≠ 0 by linarith [show 1 ≤ sqrt (b * c) by simp [h₆]]]
        rw [mul_sub, <-pow_two, sq_sqrt (by nlinarith)]
        ring
  by_cases h₉ : sqrt (b * c) ≥ 2
  . -- Suppose that √(bc) ≥ 2.
    -- Break the goal into three parts.
    refine ⟨?_, Iff.intro ?_ ?_⟩
    . -- √(bc)(a + 1) ≥ 2 is trivial.
      nlinarith
    . -- Equality implies a = 0 and b = c = 2.
      intro h
      have ha : a ≤ 0 := by
        by_contra!
        nlinarith
      replace ha : a = 0 := by
        linarith
      simp [ha] at h h₃
      rw [<-sq_eq_sq₀ (by nlinarith) (by nlinarith), sq_sqrt (by nlinarith)] at h
      -- Since bc = b + c = 4, b = c = 2.
      have h₁₀ : (b - 2) * (c - 2) = 0 := by
        linarith
      simp at h₁₀
      right
      obtain h₁₀ | h₁₀ := h₁₀
      all_goals
        exact ⟨ha, by linarith, by linarith⟩
    . -- Checking the solution indeed satisfies the equality.
      intro h
      obtain ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ := h
      all_goals
        simp [ha, hb, hc]
        try norm_num
  . -- Suppose that √(bc) < 2.
    -- Show a lemma that -x³ + 4x² - 5x + 2 = (2 - x)(x - 1)².
    have lm₀ (x : ℝ) : -x ^ 3 + 4 * x ^ 2 - 5 * x + 2 = (2 - x) * (x - 1) ^ 2 := by
      ring
    -- Break the goal into three parts.
    refine ⟨?_, Iff.intro ?_ ?_⟩
    . -- Show that √(bc)(a + 1) ≥ 2.
      calc
        sqrt (b * c) * (a + 1) ≥ sqrt (b * c) * ((sqrt (b * c) * (2 - sqrt (b * c))) / (2 * sqrt (b * c) - 1) + 1) := by
          rw [ge_iff_le, mul_le_mul_left (by simp; linarith only [h₆])]
          linarith only [h₈]
        _ ≥ 2 := by
          have : 2 * sqrt (b * c) - 1 > 0 := by
            linarith [show 1 ≤ sqrt (b * c) by simp [h₆]]
          rw [ge_iff_le, div_add_one this.ne', <-mul_div_assoc, le_div_iff₀ this]
          -- Use lemma to simplify the inequality.
          suffices 0 ≤ (2 - sqrt (b * c)) * (sqrt (b * c) - 1) ^ 2 by
            linarith [lm₀ (sqrt (b * c))]
          rw [mul_comm, mul_nonneg_iff_of_pos_right (by linarith only [h₉])]
          exact sq_nonneg (sqrt (b * c) - 1)
    . -- Show that √(bc)(a + 1) = 2 implies a = b = c = 1.
      intro h
      -- Note that √(bc)(a + 1) ≥ √(bc)((√(bc)(2 - √(bc)))/(2√(bc) - 1) + 1) ≥ 2 = √(bc)(a + 1) implies that all inequality must be indeed equality.
      have h₁₀ : sqrt (b * c) * (a + 1) ≥ sqrt (b * c) * ((sqrt (b * c) * (2 - sqrt (b * c))) / (2 * sqrt (b * c) - 1) + 1) := by
        rw [ge_iff_le, mul_le_mul_left (by simp; linarith only [h₆])]
        linarith only [h₈]
      replace h₁₀ : sqrt (b * c) * ((sqrt (b * c) * (2 - sqrt (b * c))) / (2 * sqrt (b * c) - 1) + 1) ≤ 2 := by
        linarith
      -- Rewrite the inequality to 0 ≥ (2 - √(bc))(√(bc) - 1)².
      replace h₁₀ : (2 - sqrt (b * c)) * (sqrt (b * c) - 1) ^ 2 ≤ 0 := by
        have : 2 * sqrt (b * c) - 1 > 0 := by
          linarith [show 1 ≤ sqrt (b * c) by simp [h₆]]
        rw [div_add_one this.ne', <-mul_div_assoc, div_le_iff₀ this] at h₁₀
        linarith [lm₀ (sqrt (b * c))]
      -- However, 0 ≤ (2 - √(bc))(√(bc) - 1)².
      have h₁₀' : 0 ≤ (2 - sqrt (b * c)) * (sqrt (b * c) - 1) ^ 2 := by
        rw [mul_comm, mul_nonneg_iff_of_pos_right (by linarith only [h₉])]
        exact sq_nonneg (sqrt (b * c) - 1)
      -- Therefore, (2 - √(bc))(√(bc) - 1)² = 0.
      replace h₁₀ : (2 - sqrt (b * c)) * (sqrt (b * c) - 1) ^ 2 = 0 := by
        linarith only [h₁₀, h₁₀']
      -- Now √(bc) = 1.
      simp [show 2 - sqrt (b * c) ≠ 0 by linarith only [h₉]] at h₁₀
      replace h₁₀ : sqrt (b * c) = 1 := by
        linarith only [h₁₀]
      clear h₁₀'
      -- Now a ≥ 1.
      simp [h₁₀] at h₈
      norm_num at h₈
      simp at h₁₀
      clear h₆
      -- Now b = c = 1.
      have hc : c = 1 := by
        linarith only [show 1 ≤ c by linarith, show 1 ≥ c by nlinarith]
      simp [hc] at h₁₀
      -- Now a = 1.
      have ha : a = 1 := by
        linarith
      left
      exact ⟨ha, h₁₀, hc⟩
    . -- Checking the solution indeed satisfies the equality.
      intro h
      obtain ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ := h
      all_goals
        simp [ha, hb, hc]
        try norm_num
    
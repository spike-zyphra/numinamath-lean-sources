import Mathlib

open Real Set

/- 29 Given that $\alpha, \beta, \gamma$ are all acute angles, $\cos ^{2} \alpha+\cos ^{2} \beta+\cos ^{2} \gamma=1$, prove that: $\frac{3 \pi}{4}<\alpha+\beta+\gamma<\pi$. -/
theorem inequalities_291912 (α β γ : ℝ) (h₀ : α ∈ Ioo 0 (π / 2)) (h₁ : β ∈ Ioo 0 (π / 2))
    (h₂ : γ ∈ Ioo 0 (π / 2)) (h₃ : cos α ^ 2 + cos β ^ 2 + cos γ ^ 2 = 1) :
    3 * π / 4 < α + β + γ ∧ α + β + γ < π := by
  -- if cos a ^ 2 + cos b ^ 2 + cos c ^ 2 = 1 then
  -- -cos (a - b) * cos (a + b) = -(cos a * cos b + sin a * sin b) * (cos a * cos b - sin a * sin b)
  --          = -cos a ^ 2 * cos b ^ 2 + sin a ^ 2 * sin b ^ 2
  --          = -cos a ^ 2 * cos b ^ 2 + (1 - cos a ^ 2) * (1 - cos b ^ 2)
  --          = 1 - cos a ^ 2 - cos b ^ 2 = cos c ^ 2
  have h1 {a b c} (h : cos a ^ 2 + cos b ^ 2 + cos c ^ 2 = 1) : cos c ^ 2 = -cos (a - b) * cos (a + b) := by
    rw [cos_sub, cos_add]
    ring_nf
    rw [sin_sq, sin_sq]
    linear_combination h
  -- show that if cos a ^ 2 + cos b ^ 2 + cos c ^ 2 = 1
  -- and a ∈ (0, π / 2), b ∈ (0, π / 2), c ∈ (0, π / 2)
  -- then π / 2 < a + b
  have h2 {a b c} (ha : a ∈ Ioo 0 (π / 2)) (hb : b ∈ Ioo 0 (π / 2)) (hc : c ∈ Ioo 0 (π / 2))
        (h : cos a ^ 2 + cos b ^ 2 + cos c ^ 2 = 1) : π / 2 < a + b := by
    -- we have cos c ^ 2 = -cos(a - b) * cos (a + b)
    replace h1 := h1 h
    -- suppose that a + b ≤ π / 2 and show that cos c ^ 2 > -cos(a - b) * cos (a + b)
    contrapose! h1
    apply ne_of_gt
    simp only [mem_Ioo] at ha hb h hc
    apply lt_of_le_of_lt (b := 0)
    -- show that -cos(a - b) * cos(a + b) ≤ 0
    · rw [neg_mul, neg_nonpos]
      apply mul_nonneg
      -- we have 0 ≤ cos (a - b) (because -π / 2 < a - b < π / 2)
      · apply cos_nonneg_of_mem_Icc
        simp only [mem_Icc]
        constructor <;> linarith
      -- we have 0 ≤ cos (a + b) (because 0 < a + b ≤ π / 2)
      · apply cos_nonneg_of_mem_Icc
        simp only [mem_Icc]
        constructor <;> linarith
    -- we have 0 < cos c ^ 2 (because 0 < c < π / 2)
    · apply sq_pos_of_pos
      apply cos_pos_of_mem_Ioo
      simp only [mem_Ioo]
      constructor <;> linarith
  -- we get π / 2 < α + β
  have hab := h2 h₀ h₁ h₂ h₃
  constructor
  · have := h2 h₀ h₂ h₁ (by linarith)
    have := h2 h₁ h₂ h₀ (by linarith)
    -- we also get π / 2 < α + γ and π / 2 < β + γ
    -- it follows that 3 * π / 4 < α + β + γ
    linarith
  · replace h1 := h1 h₃
    -- now show that α + β + γ < π
    simp_rw [mem_Ioo] at h₀ h₁ h₂
    -- we have cos (α + β) < 0 because π / 2 < α + β < π
    have hcab : cos (α + β) < 0 := by
      apply cos_neg_of_pi_div_two_lt_of_lt hab
      linarith
    -- we have 0 < cos γ because 0 < γ < π / 2
    have hc : 0 < cos γ := by
      apply cos_pos_of_mem_Ioo
      constructor <;> linarith
    -- show that cos (α + β) ^ 2 < cos γ ^ 2
    have h3 : cos (α + β) ^ 2 < cos γ ^ 2 := calc
      -- we have cos (α + β) ^ 2 < cos (α + β) ^ 2 - cos (α + β) * (2 * cos α * cos β)
      -- because cos (α + β) < 0, 0 < cos α and 0 < cos β
      cos (α + β) ^ 2 < cos (α + β) ^ 2 - cos (α + β) * (2 * cos α * cos β) := by
          have h (x y : ℝ) : x < x - y ↔ y < 0 := by
            constructor <;> (intro h; linarith)
          rw [h]
          apply mul_neg_of_neg_of_pos hcab
          rw [mul_assoc]
          apply mul_pos zero_lt_two
          apply mul_pos
          all_goals {
            apply cos_pos_of_mem_Ioo
            rw [mem_Ioo]; constructor <;> linarith
          }
      -- we have 2 * cos α * cos β = cos (α - β) + cos (α + β)
      _ = cos (α + β) ^ 2 - cos (α + β) * (cos (α - β) + cos (α + β)) := by
          rw [two_mul_cos_mul_cos]
      -- the result follows from h1: cos γ ^ 2 = -cos (α - β) * cos (α + β)
      _ = -cos (α - β) * cos (α + β) := by ring
      _ = cos γ ^ 2 := h1.symm
    -- cos (α + β) ^ 2 < cos γ ^ 2 implies -cos(α + β) < cos γ
    rw [sq_lt_sq, abs_of_neg hcab, abs_of_pos hc] at h3
    -- -cos (α + β) = cos (π - (α + β))
    rw [←Real.cos_pi_sub] at h3
    -- suppose that π ≤ α + β + γ and show that cos γ ≤ cos (π - (α + β))
    contrapose! h3
    -- it is enough to show that π - (α + β) ≤ γ, 0 ≤ π - (α + β), and γ ≤ π
    apply cos_le_cos_of_nonneg_of_le_pi <;> linarith
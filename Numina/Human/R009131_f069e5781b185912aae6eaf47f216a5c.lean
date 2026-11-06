import Mathlib

open Real Set
open scoped BigOperators

/-Let $0 \le a,$ $b,$ $c,$ $d \le 1.$  Find the possible values of the expression
\[\sqrt{a^2 + (1 - b)^2} + \sqrt{b^2 + (1 - c)^2} + \sqrt{c^2 + (1 - d)^2} + \sqrt{d^2 + (1 - a)^2}.\]-/
theorem algebra_11529 :
  {x : ℝ | ∃ a b c d : ℝ, a ∈ Icc 0 1 ∧ b ∈ Icc 0 1 ∧ c ∈ Icc 0 1 ∧ d ∈ Icc 0 1 ∧
    x = sqrt (a^2 + (1 - b)^2) + sqrt (b^2 + (1 - c)^2) +
      sqrt (c^2 + (1 - d)^2) + sqrt (d^2 + (1 - a)^2)} =
  Icc (2 * sqrt 2) 4 := by
  simp [Icc]
  ext x
  simp
  -- goal devides into two parts
  apply Iff.intro <;> intro h
  -- prove the upperBounds and lowerBounds
  . obtain ⟨a, ha, b, hb, c, hc, d ,hd, hx⟩ := h
    refine ⟨?_, ?_⟩
    -- prove the lowerBounds
    . -- prove the qm_am inequality
      have qm_am(a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : (a + (1 - b)) / 2 ≤ √((a ^ 2 + (1 - b) ^ 2) / 2) := by
        rw [@Real.le_sqrt] -- square both sides
        have am_gm : 2 * a * (1 - b) ≤ a ^ 2 + (1 - b) ^ 2 := by
          linarith only [show 0 ≤ (a - (1 - b)) ^ 2 by positivity]
        calc
          ((a + (1 - b)) / 2) ^ 2 = 1 / 4 * a ^ 2 + 1 / 4 * (1 - b) ^ 2 + 1 / 4 * (2 * a * (1 - b)) := by ring_nf
          _ ≤ 1 / 4 * a ^ 2 + 1 / 4 * (1 - b) ^ 2 + 1 / 4 * (a ^ 2 + (1 - b) ^ 2) := by linarith only [am_gm]
          _ = (a ^ 2 + (1 - b) ^ 2) / 2 := by ring_nf
        linarith only [ha, hb]
        positivity

      -- we have (a + (1 - b)) / √2 ≤ √(a ^ 2 + (1 - b) ^ 2) by qm_am inequality
      have ineq1(a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : (a + (1 - b)) * (1 / √2) ≤ √(a ^ 2 + (1 - b) ^ 2) := by
        have ineq := qm_am a b ha hb
        calc
          (a + (1 - b)) * (1 / √2) = (a + (1 - b)) / 2 * √2 := by field_simp; rw [mul_assoc, @Real.mul_self_sqrt 2]; positivity
          _ ≤ √((a ^ 2 + (1 - b) ^ 2) / 2) * √2 := by apply mul_le_mul; exact ineq; norm_num; positivity; positivity
          _ = √(a ^ 2 + (1 - b) ^ 2) := by field_simp

      -- repeat using the ineq1, so that we have x ≥ (a + (1 - b) + b + (1 - c) + c + (1 - d) + d + (1 - a)) / √2
      have ineq_low : √(a ^ 2 + (1 - b) ^ 2) + √(b ^ 2 + (1 - c) ^ 2) + √(c ^ 2 + (1 - d) ^ 2) + √(d ^ 2 + (1 - a) ^ 2)
          ≥ (a + (1 - b)) * (1 / √2) + (b + (1 - c)) * (1 / √2) + (c + (1 - d)) * (1 / √2) + (d + (1 - a)) * (1 / √2) := by
        have ineq_ab := ineq1 a b ha hb
        have ineq_bc := ineq1 b c hb hc
        have ineq_cd := ineq1 c d hc hd
        have ineq_da := ineq1 d a hd ha

        repeat apply add_le_add
        repeat assumption

      --simplify the ineq1, so that x ≥ 2 * √2
      clear qm_am ineq1
      rw [<-hx] at ineq_low
      ring_nf at ineq_low
      calc --calculate (√2)⁻¹ * 4 = 2 * √2
        x ≥ (√2)⁻¹ * 4 := by exact ineq_low
        _ = (√2)⁻¹ * 2 * 2 := by ring_nf
        _ = (√2)⁻¹ * (√2 * √2) * 2 := by rw [@Real.mul_self_sqrt 2]; positivity
        _ = 2 * √2 := by field_simp; ring_nf

    -- prove the upperBounds
    . -- prove √(a ^ 2 + (1 - b) ^ 2) ≤ a + (1 - b)
      have ineq1(a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1) : √(a ^ 2 + (1 - b) ^ 2) ≤ a + (1 - b):= by
        rw [@Real.sqrt_le_left]
        calc
          a ^ 2 + (1 - b) ^ 2 ≤ a ^ 2 + 2 * a * (1 - b) + (1 - b) ^ 2 := by nlinarith only [ha, hb]
          _ = (a + (1 - b)) ^ 2 := by ring_nf
        linarith only [ha, hb]

      -- repeat using ineq1, so that x ≤ a + (1 - b) + b + (1 - c) + c + (1 - d) + d + (1 - a)
      have ineq_up : √(a ^ 2 + (1 - b) ^ 2) + √(b ^ 2 + (1 - c) ^ 2) + √(c ^ 2 + (1 - d) ^ 2) + √(d ^ 2 + (1 - a) ^ 2)
          ≤ (a + (1 - b)) + (b + (1 - c)) + (c + (1 - d)) + (d + (1 - a)) := by
        have ineq_ab := ineq1 a b ha hb
        have ineq_bc := ineq1 b c hb hc
        have ineq_cd := ineq1 c d hc hd
        have ineq_da := ineq1 d a hd ha

        repeat apply add_le_add
        repeat assumption

      -- simplify the ineq_up to x ≤ 4
      clear ineq1
      rw [<-hx] at ineq_up
      ring_nf at ineq_up
      exact ineq_up

  -- prove all elements of Icc (2 * √2) 4 can be taken
  . -- first prove the positiveness of x
    have hx0 : 0 ≤ x := by linarith only [show 0 ≤ 2 * √2 by positivity, h]

    -- prove the answer t = (4 + √(2 * x ^ 2 - 16)) / 8 satisfied t ∈ Icc 0 1
    have hx₁ : 0 ≤ (4 + √(2 * x ^ 2 - 16)) / 8 ∧ (4 + √(2 * x ^ 2 - 16)) / 8 ≤ 1 := by
      refine ⟨?_, ?_⟩
      -- prove positiveness of (4 + √(2 * x ^ 2 - 16)) / 8
      . positivity
      -- less than 1
      . -- convert to proof of positiveness
        have hx₂ : 0 ≤ (4 - √(2 * x ^ 2 - 16)) / 8 := by
          apply div_nonneg
          -- prove √(2 * x ^ 2 - 16) ≤ 4
          have ineq : √(2 * x ^ 2 - 16) ≤ 4 := by
            rw [@Real.sqrt_le_left]
            calc
              2 * x ^ 2 - 16 ≤ 2 * 4 ^ 2 - 16 := by linarith only [show x ^ 2 ≤ 4 ^ 2 by apply sq_le_sq'; linarith only [hx0]; tauto]
              _ = 16 := by norm_num
            norm_num
            positivity

          linarith only [ineq]
          positivity

        calc
          (4 + √(2 * x ^ 2 - 16)) / 8 = 1 - (4 - √(2 * x ^ 2 - 16)) / 8 := by ring_nf
          _ ≤ 1 := by linarith only [hx₂]

    -- using a = b = c = d = t = (4 + √(2 * x ^ 2 - 16)) / 8
    use ((4 + √(2 * x ^ 2 - 16)) / 8)
    simp [hx₁]
    use ((4 + √(2 * x ^ 2 - 16)) / 8)
    simp [hx₁]
    use ((4 + √(2 * x ^ 2 - 16)) / 8)
    simp [hx₁]
    use ((4 + √(2 * x ^ 2 - 16)) / 8)
    simp [hx₁]
    ring_nf

    -- prove x ^ 2 ≥ 8 (x ≥ 2 * √2 is hard to use)
    have ineq1 : 8 ≤ x ^ 2 := by
      calc
        8 = 4 * 2 := by norm_num
        _ = 4 * (√2 ^ 2) := by rw [@Real.sq_sqrt]; positivity
        _ = (2 * √2) ^ 2 := by ring_nf
        _ ≤ x ^ 2 := by apply sq_le_sq'; linarith only [hx0, show 0 ≤ 2 * √2 by positivity]; tauto

    -- calculate the result step by step
    symm
    calc
      √(1 / 2 + √(-16 + x ^ 2 * 2) ^ 2 * (1 / 32)) * 4 = √(1 / 2 + (-16 + x ^ 2 * 2) * (1 / 32)) * 4 := by rw [@Real.sq_sqrt]; linarith only [ineq1]
      _ = √(x ^ 2 * (1 / 16)) * 4 := by ring_nf
      _ = √(x ^ 2 * (1 / 16) * 4 ^ 2) := by field_simp
      _ = √(x ^ 2) := by norm_num
      _ = x := by rw [@Real.sqrt_sq]; positivity

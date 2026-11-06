import Mathlib

open Real

/-Let $0 \le a,$ $b,$ $c \le 1.$  Find the maximum value of
\[\sqrt{abc} + \sqrt{(1 - a)(1 - b)(1 - c)}.\]-/
theorem algebra_15360 :
    -- sqrt (a * b * c) + sqrt ((1 - a) * (1 - b) * (1 - c)) ≤ 1 ∧
    -- ∃x, ∃y, ∃z, 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ z ∧ z ≤ 1 ∧ √(x * y * z) + √((1 - x) * (1 - y) * (1 - z)) = 1
    IsGreatest { x | ∃(a b c : ℝ), 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1 ∧ x = √(a * b * c) + √((1 - a) * (1 - b) * (1 - c)) } 1 := by
  unfold IsGreatest
  constructor
  · -- 1 is in the set
    repeat use 0; simp
  · -- 1 is the greatest element
    apply mem_upperBounds.mpr
    simp
    intro x 
    intro a ha₁ ha₂
    intro b hb₁ hb₂
    intro c hc₁ hc₂
    intro hx
    rw [hx]
    apply le_trans
    -- Since $0 \le c \le 1,$ $\sqrt{c} \le 1$ and $\sqrt{1 - c} \le 1,$ so \[\sqrt{abc} + \sqrt{(1 - a)(1 - b)(1 - c)} \le \sqrt{ab} + \sqrt{(1 - a)(1 - b)}.\]
    case b => exact √(a * b) + √((1 - a) * (1 - b))
    apply add_le_add
    apply sqrt_le_sqrt
    rw [mul_assoc]
    by_cases h: a = 0
    . rw [h]
      linarith
    rw [mul_le_mul_left (lt_of_le_of_ne ha₁ (Ne.symm h))]
    rw (config := { occs := .pos [2] }) [←mul_one b]
    by_cases h: b = 0
    . rw [h]
      simp
    rw [mul_le_mul_left (lt_of_le_of_ne hb₁ (Ne.symm h))]
    exact hc₂

    apply sqrt_le_sqrt
    rw [mul_assoc]
    by_cases h: a = 1
    . rw [h]
      linarith
    rw [mul_le_mul_left (by linarith [lt_of_le_of_ne ha₂ h])]
    rw (config := { occs := .pos [2] }) [←mul_one (1 - b)]
    by_cases h: b = 1
    . rw [h]
      simp
    rw [mul_le_mul_left (by linarith [lt_of_le_of_ne hb₂ h])]
    linarith

    -- Then by AM-GM
    -- \[\sqrt{ab} \le \frac{a + b}{2}\]
    have ine₁ : √(a * b) ≤ (a + b) / 2 := by
      rw [Real.sqrt_le_iff]
      use (by linarith)
      have : ((a + b) / 2) ^ 2 = (a^2 + b^2 + 2 * a * b) / 4 := by ring_nf
      rw [this]
      have : 0 ≤ (a^2 + b^2 - 2 * a * b) / 4 := by
        have : (a - b)^2 = a^2 + b^2 - 2 * a * b := by ring_nf
        rw [this.symm]
        positivity
      linarith

    -- and \[\sqrt{(1 - a)(1 - b)} \le \frac{(1 - a) + (1 - b)}{2} = \frac{2 - a - b}{2},\]
    have ine₂ : √((1 - a) * (1 - b)) ≤ (2 - a - b) / 2 := by
      rw [Real.sqrt_le_iff]
      use (by linarith)
      obtain ⟨p, hp⟩ := show ∃p, p = 1 - a by simp
      obtain ⟨q, hq⟩ := show ∃q, q = 1 - b by simp
      rw [show 2 - a - b = 1 - a + (1 - b) by linarith, hp.symm, hq.symm]
      have : ((p + q) / 2) ^ 2 = (p^2 + q^2 + 2 * p * q) / 4 := by ring_nf
      rw [this]
      have : 0 ≤ (p^2 + q^2 - 2 * p * q) / 4 := by
        have : (p - q)^2 = p^2 + q^2 - 2 * p * q := by ring_nf
        rw [this.symm]
        positivity
      linarith
    rw (config := { occs := .pos [3]} ) [show 1 = (a + b) / 2 + (2 - a - b) / 2 by linarith]
    apply add_le_add
    exact ine₁
    exact ine₂


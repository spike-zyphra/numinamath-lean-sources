import Mathlib

theorem algebra_9196 (a : ℝ) :
    (∃! x : ℝ, 0 ≤ x^2 + a * x + 6 ∧ x^2 + a * x + 6 ≤ 4) ↔
    a = 2 * √2 ∨ a = -2 * √2 := by
-- Prove both implications
  constructor <;> intro h
  . -- It suffices to prove that a^2 = 8
    suffices h : a ^ 2 = 8 by
      rw [show 8 = (2 * √2) ^ 2 by ring_nf; norm_num] at h
      by_contra!
      nlinarith (config := {splitNe := true})
    -- Rewrite the inequalities by completing the square
    have h1 (x : ℝ) : 0 ≤ x^2 + a * x + 6 ↔ (x + a/2)^2 ≥ a^2/4 - 6 := by
      constructor <;> intro h <;> linarith
    have h2 (x : ℝ) : x^2 + a * x + 6 ≤ 4 ↔ (x + a/2)^2 ≤ a^2/4 - 2 := by
      constructor <;> intro h <;> linarith
    conv at h =>
      congr
      ext x
      rw [h1, h2]
    clear h1 h2

    obtain ⟨x, ⟨hx1, hx2⟩, hxu⟩ := h
    simp at hxu
    -- a^2 ≥ 8 must hold, because 0 ≤ (x + a/2)^2 ≤ a^2/4 - 2
    have ha : a ^ 2 ≥ 8 := by linarith [sq_nonneg (x + a/2)]
    -- So it suffices to prove that a^2/4 - 2 ≤ 0
    suffices h : a^2/4 - 2 ≤ 0 by linarith
    -- Prove its contrapositive, suppose a^2/4 - 2 > 0
    by_contra! ha
    -- We prove that the inequality has at least two solutions, namely -a/2 ± √(a^2/4 - 2)
    have h1 := hxu (-a/2 + √(a^2/4 - 2))
    have h2 := hxu (-a/2 - √(a^2/4 - 2));
    -- Show that they are really solutions
    simp [show (-a / 2 + √(a^2/4 - 2) + a / 2) ^ 2 = a^2/4 - 2 by ring_nf; apply Real.sq_sqrt; linarith] at h1
    simp [show (-a / 2 - √(a^2/4 - 2) + a / 2) ^ 2 = a^2/4 - 2 by ring_nf; apply Real.sq_sqrt; linarith] at h2
    simp [show a ^ 2 / 4 ≤ a ^ 2 / 4 - 2 + 6 by linarith] at h1 h2
    -- Show that they are different
    subst h2
    replace ha : √(a ^ 2 / 4 - 2) > 0 := by positivity
    linarith

  . -- We prove that if a = ± 2√2, then the inequality has exactly one solution
    obtain ha | ha := h
    . -- Assume that a = 2√2
      use -Real.sqrt 2
      constructor
      . -- Show that it indeed satisfies 0 ≤ x^2 + a*x + 6 ≤ 4
        have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have h2 : (-Real.sqrt 2) ^ 2 = 2 := by nlinarith [Real.sqrt_nonneg 2, h1]
        simp [ha, h1, h2]
        ring_nf
        norm_num
      . -- Show that it is unique
        intro y hy
        have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have h2 : (-Real.sqrt 2) ^ 2 = 2 := by nlinarith [Real.sqrt_nonneg 2, h1]
        simp [ha, h1] at hy ⊢
        nlinarith [sq_nonneg (y + Real.sqrt 2)]

    . -- Assume that a = -2√2
      use Real.sqrt 2
      constructor
      . -- Show that it indeed satisfies 0 ≤ x^2 + a*x + 6 ≤ 4
        have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        have h2 : (Real.sqrt 2) ^ 2 = 2 := by nlinarith [Real.sqrt_nonneg 2, h1]
        simp [ha, h1, h2]
        ring_nf
        norm_num
      . -- Show that it is unique
        intro y hy
        have h1 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        simp [ha, h1] at hy ⊢
        nlinarith [sq_nonneg (y - Real.sqrt 2)]
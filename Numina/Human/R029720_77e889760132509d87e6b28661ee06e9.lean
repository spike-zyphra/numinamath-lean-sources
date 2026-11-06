import Mathlib

/- Theorem: Under a system of symmetric linear equations involving real variables a, b, c, d,
The equations are:
  1. ab + cd = 6
  2. ac + bd = 3
  3. ad + bc = 2
  4. a + b + c + d = 6
the only solutions to this system of equations are:
    - (0, 1, 2, 3)
    - (2, 3, 0, 1)
    - (1, 0, 3, 2)
    - (3, 2, 1, 0)-/
theorem algebra_30341 {a b c d : ℝ}
    (h₀ : a * b + c * d = 6) (h₁ : a * c + b * d = 3) (h₂ : a * d + b * c = 2)
    (h₃ : a + b + c + d = 6) :
    (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 3) ∨ (a = 2 ∧ b = 3 ∧ c = 0 ∧ d = 1) ∨
    (a = 1 ∧ b = 0 ∧ c = 3 ∧ d = 2) ∨ (a = 3 ∧ b = 2 ∧ c = 1 ∧ d = 0) := by

  -- Combine equations h₀ and h₁ to derive a new relation
  have h4 : (a + d) * (b + c) = 9 := by
    nlinarith [h₀, h₁]

  -- Combine h₀ and h₂ similarly
  have h5 : (a + c) * (b + d) = 8 := by
    nlinarith [h₀, h₂]

  -- Use total sum h₃ and h4 to isolate a + d
  have h7 : a + d = 3 := by
    have h_sum : a + b + c + d = 6 := h₃
    have eq1 : b + c = 6 - (a + d) := by linarith
    rw [eq1] at h4
    -- Solve resulting quadratic equation in (a + d)
    have : (a + d) ^ 2 - 6 * (a + d) + 9 = 0 := by nlinarith
    have : (a + d - 3) ^ 2 = 0 := by nlinarith
    have : a + d - 3 = 0 := by nlinarith
    linarith

  -- Plug into h5 and solve for (a + c)
  have h9 : (a + c) * (b + d) = 8 := h5
  have h10 : b + d = 6 - (a + c) := by linarith [h₃]
  rw [h10] at h9
  have h11 : (a + c) ^ 2 - 6 * (a + c) + 8 = 0 := by nlinarith
  have h12 : (a + c - 2) * (a + c - 4) = 0 := by
    ring_nf at h11 ⊢
    linarith

  -- Two possible cases for a + c
  cases' (mul_eq_zero.mp h12) with hac2 hac4

  · -- Case 1: a + c = 2
    have hac2' : a + c = 2 := by linarith
    have hd : d = c + 1 := by nlinarith
    have hb : b = 3 - c := by nlinarith
    have ha : a = 2 - c := by linarith [hac2']

    -- Use equation h₀ to solve for c
    have eq1 : a * b + c * d = 6 := h₀
    rw [ha, hb, hd] at eq1
    have hc : c = 0 ∨ c = 2 := by
      have eq1' : (2 - c) * (3 - c) + c * (c + 1) = 6 := by linarith
      have : 2 * c ^ 2 - 4 * c = 0 := by
        ring_nf at eq1'
        linarith
      have : c * (c - 2) = 0 := by linarith
      cases' (mul_eq_zero.mp this) with hc1 hc2
      · left; linarith
      · right; linarith

    -- Subcases from above: c = 0 or c = 2
    cases' hc with hc0 hc2

    · -- Subcase: c = 0
      have ha2 : a = 2 := by rw [ha]; linarith [hc0]
      have hb3 : b = 3 := by rw [hb]; linarith [hc0]
      have hd1 : d = 1 := by rw [hd]; linarith [hc0]
      right; left
      exact ⟨ha2, hb3, hc0, hd1⟩

    · -- Subcase: c = 2
      have ha0 : a = 0 := by rw [ha]; linarith [hc2]
      have hb1 : b = 1 := by rw [hb]; linarith [hc2]
      have hd3 : d = 3 := by rw [hd]; linarith [hc2]
      left
      exact ⟨ha0, hb1, hc2, hd3⟩

  · -- Case 2: a + c = 4
    have hac4' : a + c = 4 := by linarith
    have hd : d = c - 1 := by nlinarith
    have hb : b = 3 - c := by nlinarith
    have ha : a = 4 - c := by linarith [hac4']

    -- Plug into equation h₀ to solve for c
    have eq1 : a * b + c * d = 6 := h₀
    rw [ha, hb, hd] at eq1
    have hc : c = 1 ∨ c = 3 := by
      have eq1' : (4 - c) * (3 - c) + c * (c - 1) = 6 := by linarith
      have : c^2 - 4 * c + 3 = 0 := by
        ring_nf at eq1'
        linarith
      have : (c - 1) * (c - 3) = 0 := by linarith
      cases' (mul_eq_zero.mp this) with hc1 hc2
      · left; linarith
      · right; linarith

    -- Subcases: c = 1 or c = 3
    cases' hc with hc1 hc3

    · -- Subcase: c = 1
      have ha3 : a = 3 := by rw [ha]; linarith [hc1]
      have hb2 : b = 2 := by rw [hb]; linarith [hc1]
      have hd0 : d = 0 := by rw [hd]; linarith [hc1]
      right; right; right
      exact ⟨ha3, hb2, hc1, hd0⟩

    · -- Subcase: c = 3
      have ha1 : a = 1 := by rw [ha]; linarith [hc3]
      have hb0 : b = 0 := by rw [hb]; linarith [hc3]
      have hd2 : d = 2 := by rw [hd]; linarith [hc3]
      right; right; left
      exact ⟨ha1, hb0, hc3, hd2⟩

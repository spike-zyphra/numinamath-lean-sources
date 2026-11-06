import Mathlib

theorem algebra_10655 (f : ℝ → ℝ) (a : ℝ) (hf : f = fun x => x ^ 2 + a * x)
    (h : ∀ x, f x = 0 ↔ f (f x) = 0) (ha : ∃ x, f x = 0) :
    0 ≤ a ∧ a < 4 := by
  rcases ha with ⟨x₀, hx₀⟩
  have h₄ : a ≥ 0 := by
    by_contra h₄
    push_neg at h₄
    -- Assume a < 0
    have h5 : a ^ 2 - 4 * a > 0 := by nlinarith
    have h6 : ∃ r : ℝ, r ^ 2 + a * r + a = 0 := by
      have h7 : a ^ 2 - 4 * a > 0 := h5
      use (-a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * a), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * a by nlinarith)]
    rcases h6 with ⟨r, hr⟩
    have h6 : f r = r ^ 2 + a * r := by
      rw [hf]
    have h7 : r ^ 2 + a * r = -a := by
      nlinarith
    have eq1 : f r = -a := by
      rw [h6]
      linarith
    have h7' : f (f r) = 0 := by
      have h8 : f r = -a := eq1
      rw [h8]
      simp [hf]
      all_goals
        nlinarith
    have h13 : f r = 0 ↔ f (f r) = 0 := h r
    have eq2' : f (f r) = 0 := h7'
    have eq3 : f r = -a := eq1
    have eq4 : f r ≠ 0 := by
      linarith [eq3, show a ≠ 0 by nlinarith]
    have h17 : (f r = 0) ↔ (f (f r) = 0) := h13
    rw [show f (f r) = (0 : ℝ) by linarith [eq2']] at h17
    have eq5 : f r = 0 := by
      tauto
    contradiction
  have ha4 : a < 4 := by
    by_contra h₄
    push_neg at h₄
    have h5 : a ^ 2 - 4 * a ≥ 0 := by nlinarith
    have h6 : ∃ r : ℝ, r ^ 2 + a * r + a = 0 := by
      have h7 : a ^ 2 - 4 * a ≥ 0 := h5
      use (-a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 4 * a), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * a by nlinarith)]
    rcases h6 with ⟨r, hr⟩
    have h6 : f r = r ^ 2 + a * r := by
      rw [hf]
    have h7 : r ^ 2 + a * r = -a := by
      nlinarith
    have eq1 : f r = -a := by
      rw [h6]
      linarith
    have h7' : f (f r) = 0 := by
      have h8 : f r = -a := eq1
      rw [h8]
      simp [hf]
      all_goals
        nlinarith
    have h13 : f r = 0 ↔ f (f r) = 0 := h r
    have eq2' : f (f r) = 0 := h7'
    have eq3 : f r = -a := eq1
    have eq4 : f r ≠ 0 := by
      nlinarith [eq3, show a ≠ 0 by nlinarith]
    -- e'll reach a contradiction. The hypothesis h r states f r = 0 ↔ f (f r) = 0
    have h17 : (f r = 0) ↔ (f (f r) = 0) := h13
    rw [show f (f r) = (0 : ℝ) by linarith [eq2']] at h17
    have eq5 : f r = 0 := by
      tauto
    contradiction
  constructor
  · linarith
  · linarith
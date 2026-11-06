import Mathlib

theorem algebra_272262 (f : ℝ → ℝ) (a : ℝ) (hf : f = fun x => x^2 + a * x)
    (h : ∀ x, f x = 0 ↔ f (f x) = 0) (ha : ∃ x, f x = 0) :
    0 ≤ a ∧ a ≤ 4 := by 
  have ha0 : 0 ≤ a := by
    by_contra ha1
    push_neg at ha1
    have ha2 : a ^ 2 - 4 * a > 0 := by
      nlinarith
    have ha4 : ∃ x : ℝ, x ^ 2 + a * x + a = 0 := by
      have h5 : a ^ 2 - 4 * a > 0 := ha2
      use (-a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_pos.mpr (show a ^ 2 - 4 * a > 0 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * a by nlinarith)]
    rcases ha4 with ⟨x, hx⟩
    have hx2 : f x = -a := by
      rw [hf]
      simp
      nlinarith
    have hx3 : f (f x) = 0 := by
      rw [hx2]
      rw [hf]
      simp
      all_goals nlinarith
    have hx4 : f x = 0 := by
      have hx5 : f x = 0 ↔ f (f x) = 0 := h x
      have hx6 : f (f x) = 0 := hx3
      tauto
    rw [hx2] at hx4
    nlinarith
  have ha1 : a ≤ 4 := by
    by_contra ha2
    push_neg at ha2
    have ha2 : a ^ 2 - 4 * a > 0 := by
      nlinarith
    have ha4 : ∃ x : ℝ, x ^ 2 + a * x + a = 0 := by
      have h5 : a ^ 2 - 4 * a > 0 := ha2
      use (-a + Real.sqrt (a ^ 2 - 4 * a)) / 2
      nlinarith [Real.sqrt_pos.mpr (show a ^ 2 - 4 * a > 0 by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 - 4 * a by nlinarith)]
    rcases ha4 with ⟨x, hx⟩
    have hx2 : f x = -a := by
      rw [hf]
      simp
      nlinarith
    have hx3 : f (f x) = 0 := by
      rw [hx2]
      rw [hf]
      simp
      all_goals nlinarith
    have hx4 : f x = 0 := by
      have hx5 : f x = 0 ↔ f (f x) = 0 := h x
      have hx6 : f (f x) = 0 := hx3
      tauto
    rw [hx2] at hx4
    nlinarith
  constructor
  · exact ha0
  · exact ha1
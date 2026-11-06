import Mathlib

theorem algebra_167736 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y)
    (h0 : f 0 ≠ 0) :
    f 0 = 1 ∧ (∀ y, f y = f (-y)) ∧ (∀ c, f (c / 2) = 0 → (∀ x, f (x + c) = -f x) ∧ f.Periodic (2 * c)) := by
  have h1 : f 0 = 1 := by
    have h2 := h 0 0
    norm_num at h2
    have h3 : f 0 * (f 0 - 1) = 0 := by linarith
    cases (mul_eq_zero.1 h3) with
    | inl h4 => 
      exfalso 
      exact h0 h4
    | inr h5 => 
      linarith
  have h2 : ∀ y, f y = f (-y) := by
    intro y
    have h3 := h 0 y
    norm_num at h3
    rw [h1] at h3
    linarith
  constructor
  · exact h1
  constructor
  · exact h2
  · intro c hc
    constructor 
    · -- Prove that for any x, f(x + c) = -f(x)
      intro x 
      have h4 := h (x + c / 2) (c / 2)
      have eq1 : (x + c / 2 + c / 2) = x + c := by ring
      have eq2 : (x + c / 2 - (c / 2)) = x := by ring
      rw [eq1, eq2] at h4
      have h7 : f (x + c) = -f x := by 
        rw [hc] at h4 
        linarith 
      exact h7 
    · -- Show that f is periodic with period 2 * c 
      unfold Function.Periodic 
      intro x
      have h7 : ∀ x, f (x + c) = -f x := by 
        intro x 
        have h4 := h (x + c / 2) (c / 2)
        have eq1 : (x + c / 2 + c / 2) = x + c := by ring
        have eq2 : (x + c / 2 - (c / 2)) = x := by ring
        rw [eq1, eq2] at h4
        have h7 : f (x + c) = -f x := by 
          rw [hc] at h4 
          linarith 
        exact h7 
      calc 
        f (x + 2 * c) = f ((x + c) + c) := by ring_nf 
        _ = -f (x + c) := by 
          rw [h7] 
        _ = -(-f x) := by 
          rw [h7] 
        _ = f x := by ring
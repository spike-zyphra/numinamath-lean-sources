import Mathlib

theorem algebra_229289 (f : ℝ → ℝ) (h : ∀ x y, f (x + y) + f (x - y) = 2 * f x * f y)
    (hc : ∃ c > 0, f (c / 2) = 0) :
    ∃ c, c > 0 ∧ Function.Periodic f (2 * c) := by
  rcases hc with ⟨c, hc_pos, hfc⟩
  have h0 : f 0 * (1 - f 0) = 0 := by
    have h1 := h 0 0
    norm_num at h1
    nlinarith
  have h1 : f 0 = 0 ∨ f 0 = 1 := by 
    cases (mul_eq_zero.mp h0) with
    | inl h2 => 
        left
        linarith
    | inr h3 => 
        right
        linarith
  cases h1 with
  | inl hf0 =>
    have h2 : ∀ x : ℝ, f x = 0 := by
      intro x
      have h3 := h x 0
      simp [hf0] at h3
      linarith
    use (1 : ℝ)
    constructor
    · norm_num
    · unfold Function.Periodic
      intro x
      simp [h2]
  | inr hf0 =>
    have h3 : ∀ x, f (x + c / 2) + f (x - c / 2) = 0 := by
      intro x
      have h4 := h x (c / 2)
      rw [hfc] at h4
      norm_num at h4 ⊢
      linarith
    have hf1 : f c = -1 := by
      have h4 := h (c / 2) (c / 2)
      have h5 : (c / 2 : ℝ) + (c / 2 : ℝ) = c := by ring_nf
      have h6 : (c / 2 : ℝ) - (c / 2 : ℝ) = (0 : ℝ) := by ring_nf
      rw [h5, h6] at h4
      rw [hf0, hfc] at h4
      linarith
    have h4 : ∀ x, f (x + c) = - f x := by
      intro x
      have h5 : f ((x + c / 2) + c / 2) + f ((x + c / 2) - c / 2) = (0 : ℝ) := by
        apply h3
      have h6 : (x + c / 2 + c / 2 : ℝ) = (x + c : ℝ) := by
        ring_nf
      have h7 : ((x + c / 2) - c / 2 : ℝ) = (x : ℝ) := by
        ring_nf
      rw [h6, h7] at h5
      have : f (x + c) = - f x := by 
        have h8 : f (x + c) + f x = 0 := by linarith
        have : f (x + c) = - f x := by linarith
        assumption
      assumption
    use c
    constructor
    · linarith [hc_pos]
    · -- Show $2c$ is the period
      unfold Function.Periodic
      intro x
      -- Prove f(x + 2c) = f(x)
      have h8 : f (x + 2 * c) = f x := by
        calc
          f (x + 2 * c) = f ( (x + c) + c ) := by ring_nf
          _ = - f (x + c) := by rw [h4]
          _ = - (- f x) := by rw [h4]
          _ = f x := by ring_nf
      simpa using h8
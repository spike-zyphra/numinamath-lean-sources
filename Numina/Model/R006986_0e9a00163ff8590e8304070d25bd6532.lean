import Mathlib

theorem algebra_317035 (f : ℝ → ℝ) (m n : ℝ) (hf : ∀ x, f x = 2 ^ x * m + x ^ 2 + n * x)
    (h : {x | f x = 0} = {x | f (f x) = 0}) (h' : ∃ x, f x = 0) :
    0 ≤ m + n ∧ m + n < 4 := by

  have h1 : ∀ x, f x = 0 ↔ f (f x) = 0 := by
    rw [Set.ext_iff] at h
    intro x
    specialize h x
    simpa using h
  obtain ⟨x0, hx0⟩ := h'
  have hfx0 : f x0 = 0 := hx0
  have h2 := h1 x0
  rw [hfx0] at h2
  have h3 : f 0 = 0 := by
    simpa using h2
  have eq1 := hf 0
  rw [eq1] at h3
  have hm : m = 0 := by
    norm_num at h3
    linarith
  have h_eq : ∀ x, f x = x^2 + n * x := by
    intro x
    specialize hf x
    rw [hf]
    rw [hm]
    ring
  have h4 : 0 ≤ n := by
    by_contra hn
    push_neg at hn
    have h5 : ∃ x, f (f x) = 0 ∧ f x ≠ 0 := by
      -- Use a root of the quadratic equation that makes f(x) = -n
      use (-n + Real.sqrt (n ^ 2 - 4 * n)) / 2
      have eq1 : f ((-n + Real.sqrt (n ^ 2 - 4 * n)) / 2) = -n := by
        rw [h_eq]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [Real.sqrt_nonneg (n ^ 2 - 4 * n), hn]
      rw [eq1]
      have eq2 : f (-n) = 0 := by
        rw [h_eq]
        nlinarith
      constructor
      · linarith [eq2]
      · nlinarith
    obtain ⟨x, hx, hfx⟩ := h5
    have h6 := h1 x
    rw [show f (f x) = 0 by linarith [hx]] at h6
    simp at h6
    contradiction
  have h5 : n < 4 := by
    by_contra hn
    push_neg at hn
    have h6 : ∃ x, f (f x) = 0 ∧ f x ≠ 0 := by
      -- Use a root of the quadratic equation that makes f(x) = -n
      use (-n + Real.sqrt (n ^ 2 - 4 * n)) / 2
      have eq1 : f ((-n + Real.sqrt (n ^ 2 - 4 * n)) / 2) = -n := by
        rw [h_eq]
        ring_nf
        rw [Real.sq_sqrt (by nlinarith)]
        nlinarith [Real.sqrt_nonneg (n ^ 2 - 4 * n), hn]
      rw [eq1]
      have eq2 : f (-n) = 0 := by
        rw [h_eq]
        nlinarith
      constructor
      · linarith [eq2]
      · nlinarith
    obtain ⟨x, hx, hfx⟩ := h6
    have h7 := h1 x
    rw [show f (f x) = 0 by linarith [hx]] at h7
    simp at h7
    contradiction
  have hn : 0 ≤ n := h4
  have hn2 : n < 4 := h5
  have hm_n : 0 ≤ m + n := by linarith [hm, hn]
  have hm_n2 : m + n < 4 := by linarith [hm, hn2]
  exact ⟨hm_n, hm_n2⟩
import Mathlib


theorem algebra_241143 :{f : ℝ → ℝ | ∀ x y, f x + f y = f (f x * f y)} = {λ _ ↦ 0} := by
  ext f
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume f satisfies the functional equation, prove f = 0
    intro h
    have h1 : ∀ x y, f x + f y = f (f x * f y) := h
    have h2 : f 0 = 0 := by
      have h11 : f 0 + f 0 = f (f 0 * f 0) := h1 0 0
      have h12 : f (f 0 * f 0) = 2 * f 0 := by linarith
      have h13 : f (f 0 * f 0) + f (f 0 * f 0) = f (f (f 0 * f 0) * f (f 0 * f 0)) := h1 (f 0 * f 0) (f 0 * f 0)
      rw [h12] at h13
      have h14 : f (4 * (f 0) ^ 2) = 4 * f 0 := by
        ring_nf at h13 ⊢
        linarith
      have h15 : f 0 + f (4 * (f 0) ^ 2) = f (f 0 * f (4 * (f 0) ^ 2) ) := h1 0 (4 * (f 0) ^ 2)
      have h21 : f (f 0 * f (4 * (f 0) ^ 2)) = 4 * f 0 := by
        have h20 : f (4 * (f 0) ^ 2) = 4 * f 0 := h14
        have h19 : f 0 * f (4 * (f 0) ^ 2) = 4 * (f 0) ^ 2 := by
          rw [h20]
          ring
        rw [h19]
        apply h14
      have h22 : f 0 + f (4 * (f 0) ^ 2) = 4 * f 0 := by
        linarith [h15, h21]
      have h23 : f (4 * (f 0) ^ 2) = 4 * f 0 := h14
      have h24 : 5 * f 0 = 4 * f 0 := by
        linarith [h22, h23]
      linarith
    funext x
    have h3 : f x + f 0 = f (f x * f 0) := h1 x 0
    rw [h2] at h3
    simp at h3
    linarith
  · -- Assume f = 0, prove it satisfies the equation
    intro h
    intro x y
    simp [h]
import Mathlib

theorem algebra_204120 (a b c : ℝ) (h1 : a + b + c = 1) (h2 : 4*a + 2*b + c = 1/2)
    (h3 : 9*a + 3*b + c = 1/3) :
    {x : ℝ | a*x^2 + b*x + c = 1/(x : ℝ)} = {1, 2, 3} := by
  have ha : a = 1/6 := by
    ring_nf at h1 h2 h3 ⊢
    linarith
  have hb : b = -1 := by
    ring_nf at h1 h2 h3 ⊢
    linarith
  have hc : c = 11/6 := by
    ring_nf at h1 h2 h3 ⊢
    linarith
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- First, prove that if ax^2 + b x + c = 1/x, then x ∈ {1, 2, 3}
    intro h
    rw [ha, hb, hc] at h
    have h_eq : (1 / 6) * x ^ 2 + (-1) * x + (11 / 6) = 1 / x := h
    have hx : x ≠ 0 := by
      by_contra h0
      rw [h0] at h_eq
      norm_num at h_eq
    have h_eq2 : (1 / 6) * x ^ 3 + (-1) * x ^ 2 + (11 / 6) * x - 1 = 0 := by
      have hx2 : x ≠ 0 := hx
      have : x * ((1 / 6) * x ^ 2 + (-1) * x + (11 / 6)) = x * (1 / x) := by
        rw [h_eq]
      have hx3 : x * (1 / x) = 1 := by
        field_simp [hx2]
      linarith
    have h_eq3 : (x - 1) * (x - 2) * (x - 3) = 0 := by
      field_simp at h_eq2
      nlinarith
      <;> ring_nf at h_eq2
      <;> nlinarith
    cases' (mul_eq_zero.mp h_eq3) with h4 h5
    · cases' (mul_eq_zero.mp h4) with h6 h7
      · -- h6: x - 1 = 0
        left
        linarith
      · -- h7: x - 2 = 0
        right
        left
        linarith
    · -- h5: x - 3 = 0
      right
      right
      linarith
  · -- Show that if x ∈ {1, 2, 3}, then a x^2 + b x + c = 1/(x)
    rintro (rfl | rfl | rfl)
    all_goals
      rw [ha, hb, hc]
      norm_num
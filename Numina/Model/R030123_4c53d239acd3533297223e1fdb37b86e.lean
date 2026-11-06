import Mathlib

theorem algebra_282987 (a n : ℝ) (ha : 0 < a) (hn : 0 < n) :
  {x : ℝ | 0 < x ∧ a / (n + x) = (1/2) * (a / (n - x))} = {n / 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x in the left side prove right side
    rintro ⟨hx, heq⟩
    have h1 : n + x ≠ 0 := by 
      nlinarith
    have h2 : n - x ≠ 0 := by 
      by_contra h
      have eq11 : x = n := by linarith 
      rw [eq11] at heq
      field_simp [(show n + n ≠ 0 by nlinarith)] at heq ⊢ 
      all_goals nlinarith
    -- Derive the equation 2 * a * (n - x) = a * (n + x)
    have eq3 : 2 * a * (n - x) = a * (n + x) := by
      have eq6 : 2 * (a / (n + x)) = a / (n - x) := by
        have eq7 : a / (n + x) = (1 / 2) * (a / (n - x)) := heq
        nlinarith
      have h1'1 : n + x ≠ 0 := h1
      have h2'2 : n - x ≠ 0 := h2
      have eq7 : 2 * a * (n - x) = a * (n + x) := by
        have eq10 : 2 * (a / (n + x)) = a / (n - x) := eq6
        have eq8 : 2 * (a / (n + x)) * ((n + x) * (n - x)) = (a / (n - x)) * ((n + x) * (n - x)) := by
          rw [eq10]
        have eq9 : 2 * (a / (n + x)) * ((n + x) * (n - x)) = 2 * a * (n - x) := by
          have h11 : n + x ≠ 0 := h1
          have h12 : n - x ≠ 0 := h2
          field_simp [h11, h12] at *
          <;> ring
        have eq10' : (a / (n - x)) * ((n + x) * (n - x)) = a * (n + x) := by
          have h11 : n + x ≠ 0 := h1
          have h12 : n - x ≠ 0 := h2
          field_simp [h11, h12] at *
          <;> ring
        rw [eq9, eq10'] at eq8
        linarith
      exact_mod_cast eq7
    have eq4 : x = n / 3 := by
      apply (mul_left_inj' (ne_of_gt ha)).mp
      linarith [eq3]
    linarith [eq4]
  · -- Assume x = n/3 in the right side prove left side 
    intro heq
    have h_eq1 : x = n / 3 := by linarith [heq]
    constructor
    · -- Show that x > 0 
      have hx1 : 0 < x := by 
        have h_eq1' : x = n / 3 := h_eq1
        nlinarith [hn]
      linarith [hx1]
    · -- Show that a / (n + x) = (1 / 2) * (a / (n - x))
      have eq5 : x = n / 3 := h_eq1
      rw [eq5]
      field_simp [(show n + n / 3 ≠ 0 by nlinarith), (show n - n / 3 ≠ 0 by nlinarith)]
      <;> ring_nf <;> field_simp [(show n ≠ 0 by linarith)]
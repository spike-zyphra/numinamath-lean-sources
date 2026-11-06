import Mathlib

theorem number_theory_75425 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 2 * x + 7 * y ∣ 7 * x + 2 * y) :
    ∃ a, a > 0 ∧ (x, y) = (a, a) ∨ (x, y) = (4 * a, a) ∨ (x, y) = (19 * a, a) := by 
  have h1 : 2 * x + 7 * y ∣ 7 * x + 2 * y := h 
  rcases h1 with ⟨k, hk⟩ 
  have eq1 : 7 * x + 2 * y = k * (2 * x + 7 * y) := by 
    linarith 
  have h2 : k > 0 := by 
    by_contra h'
    push_neg at h'
    have : k ≤ 0 := by omega 
    have h3 : k * (2 * x + 7 * y) ≤ 0 := by 
      apply mul_nonpos_of_nonpos_of_nonneg 
      · linarith 
      · -- Show 2x + 7y ≥ 0 
        omega 
    nlinarith 
  have h3 : k < 4 := by 
    by_contra h'
    push_neg at h'
    have : k ≥ 4 := by omega 
    nlinarith 
  have h4 : k = 1 ∨ k = 2 ∨ k = 3 := by 
    omega 
  rcases h4 with h_eq1 | h_eq2 | h_eq3 
  · -- Case k = 1, which implies x = y
    have eq2 : 7 * x + 2 * y = 2 * x + 7 * y := by 
      rw [show k = 1 by linarith [h_eq1] ] at eq1 
      nlinarith 
    have eq3 : x = y := by 
      linarith 
    use x 
    left 
    constructor 
    · -- Show a > 0 
      linarith 
    · -- Show (x, y) = (a, a) 
      simp [eq3] 
  · -- Case k = 2, which implies x = 4y 
    have eq2 : 7 * x + 2 * y = 2 * (2 * x + 7 * y) := by 
      rw [show k = 2 by linarith [h_eq2] ] at eq1 
      linarith 
    have eq3 : x = 4 * y := by 
      linarith 
    use y 
    right 
    left 
    simp [eq3] 
  · -- Case k = 3, which implies x = 19y 
    have eq2 : 7 * x + 2 * y = 3 * (2 * x + 7 * y) := by 
      rw [show k = 3 by linarith [h_eq3] ] at eq1 
      linarith 
    have eq3 : x = 19 * y := by 
      linarith 
    use y 
    right 
    right 
    simp [eq3]
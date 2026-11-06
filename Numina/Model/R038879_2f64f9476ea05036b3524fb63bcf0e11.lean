import Mathlib

theorem algebra_14666 : {j : ℝ | ∃! x : ℝ, (2 * x + 7) * (x - 5) = -43 + j * x} = {5, -11} := by
  ext j
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume ∃! x : ℝ, (2 * x + 7) * (x - 5) = -43 + j * x, prove j = 5 ∨ j = -11
    intro h
    rcases h with ⟨x, ⟨hx1, hx2⟩⟩
    have eq1 : 2 * x ^ 2 + (-3 - j) * x + 8 = 0 := by
      nlinarith
    have eq2 : ∀ y : ℝ, (2 * y + 7) * (y - 5) = -43 + j * y → y = x := hx2
    have eq3 : (2 * (( (3 + j) / 2 - x )) + 7) * (( (3 + j) / 2 - x ) - 5) = -43 + j * (( (3 + j) / 2 - x )) := by
      nlinarith [eq1, sq_nonneg (x^2 - 4), sq_nonneg ((x - 2) * (x + 2)), sq_nonneg (j - 5), sq_nonneg (j + 11)]
    have eq7 : ( (3 + j) / 2 - x ) = x := by
      apply eq2
      exact eq3
    have h_eq : j = 4 * x - 3 := by
      nlinarith
    rw [show (-3 - j) = - (4 * x) by nlinarith] at eq1
    have h_eq5 : x ^ 2 = 4 := by
      nlinarith
    have h11 : x = 2 ∨ x = -2 := by
      have h1 : x ^ 2 - 4 = 0 := by linarith
      have h2 : (x - 2) * (x + 2) = 0 := by
        linarith
      cases' (mul_eq_zero.mp h2) with h3 h4
      · -- Case x - 2 = 0, so x = 2
        left
        linarith
      · -- Case x + 2 = 0, so x = -2
        right
        linarith
    cases' h11 with h11 h11
    · -- Case x = 2
      have eq4 : j = 5 := by
        rw [h11] at h_eq
        linarith
      left
      linarith
    · -- Case x = -2
      have eq5 : j = -11 := by
        rw [h11] at h_eq
        linarith
      right
      linarith
  · -- Show that if j=5 or j=-11, then exists unique solution
    rintro (h | h)
    · -- j=5
      rw [h]
      use 2
      constructor
      · -- Show that 2 is a solution
        norm_num
      · -- Show that 2 is a unique solution
        intro y hy
        have eq1 : (2 * y + 7) * (y - 5) = -43 + (5 : ℝ) * y := by
          nlinarith
        have eq2 : (y - 2) = 0 := by
          nlinarith
        linarith
    · -- j=-11
      rw [h]
      use -2
      constructor
      · -- Show that -2 is a solution
        norm_num
      · -- Show that -2 is a unique solution
        intro y hy
        have eq1 : (2 * y + 7) * (y - 5) = -43 + (-11 : ℝ) * y := by
          nlinarith
        have eq2 : (y + 2) = 0 := by
          nlinarith
        linarith
import Mathlib

theorem algebra_328133 (x : ℝ) (hx : x^2 + x ≠ 0 ∧ x^2 + 3 * x + 2 ≠ 0 ∧ x^2 + 5 * x + 6 ≠ 0 ∧ x^2 + 7 * x + 12 ≠ 0) :
    1 / (x^2 + x) + 1 / (x^2 + 3 * x + 2) + 1 / (x^2 + 5 * x + 6) + 1 / (x^2 + 7 * x + 12) = 4 / 21 ↔ x = 3 ∨ x = -7 := by
  rcases hx with ⟨hx1, hx2, hx3, hx4⟩
  constructor
  · -- Forward: if the equation holds, then x ∈ {-7, 3}
    intro h
    have eq1 : 1 / (x^2 + x) + 1 / (x^2 + 3 * x + 2) + 1 / (x^2 + 5 * x + 6) + 1 / (x^2 + 7 * x + 12) = 1 / x - 1 / (x + 4) := by
      have h1 : x ≠ 0 := by
        by_contra h1
        have h1' : x^2 + x = 0 := by
          rw [h1]
          norm_num
        contradiction
      have h2 : x + 1 ≠ 0 := by
        by_contra h2
        have h2' : x^2 + 3 * x + 2 = 0 := by
          have : x = -1 := by linarith
          rw [this]
          norm_num
        contradiction
      have h3 : x + 2 ≠ 0 := by
        by_contra h3
        have h3' : x^2 + 5 * x + 6 = 0 := by
          have : x = -2 := by linarith
          rw [this]
          norm_num
        contradiction
      have h4 : x + 3 ≠ 0 := by
        by_contra h4
        have h4' : x^2 + 7 * x + 12 = 0 := by
          have : x = -3 := by linarith
          rw [this]
          norm_num
        contradiction
      have eq1 : 1 / (x^2 + x) = 1 / x - 1 / (x + 1) := by
        field_simp [(show x ≠ 0 by assumption), (show x + 1 ≠ 0 by
          intro h'
          apply h2
          linarith
        )]
        <;> ring
      have eq2 : 1 / (x^2 + 3 * x + 2) = 1 / (x + 1) - 1 / (x + 2) := by
        field_simp [(show x + 1 ≠ 0 by
          intro h'
          apply h2
          linarith
        ), (show x + 2 ≠ 0 by
          intro h'
          apply h3
          linarith
        )]
        <;> ring
      have eq3 : 1 / (x^2 + 5 * x + 6) = 1 / (x + 2) - 1 / (x + 3) := by
        field_simp [(show x + 2 ≠ 0 by
          intro h'
          apply h3
          linarith
        ), (show x + 3 ≠ 0 by
          intro h'
          apply h4
          linarith
        )]
        <;> ring
      have eq4 : 1 / (x^2 + 7 * x + 12) = 1 / (x + 3) - 1 / (x + 4) := by
        field_simp [(show x + 3 ≠ 0 by
          intro h'
          apply h4
          linarith
        ), (show x + 4 ≠ 0 by
          by_contra h5
          have : x = -4 := by linarith
          rw [this] at hx4
          norm_num at hx4
        )]
        <;> ring
      rw [eq1, eq2, eq3, eq4]
      field_simp [(show x ≠ 0 by assumption), (show x + 4 ≠ 0 by
        by_contra h5
        have : x = -4 := by linarith
        rw [this] at hx4
        norm_num at hx4
      )]
      <;> ring
    rw [eq1] at h
    have h1' : x ≠ 0 := by
      by_contra h1
      have h1' : x^2 + x = 0 := by
        rw [h1]
        norm_num
      contradiction
    have h2' : x + 4 ≠ 0 := by
      by_contra h2
      have : x = -4 := by linarith
      rw [this] at hx4
      norm_num at hx4
    field_simp [(show x ≠ 0 by assumption), (show x + 4 ≠ 0 by assumption)] at h
    have h_eq : (x - 3) * (x + 7) = 0 := by
      nlinarith [h]
    cases' (mul_eq_zero.1 h_eq) with h5 h6
    · -- Case x - 3 = 0
      left
      linarith
    · -- Case x + 7 = 0
      right
      linarith
  · -- Backward: if x ∈ {-7, 3}, then the equation holds
    rintro (h | h)
    · -- Case x = 3
      rw [h]
      norm_num
    · -- Case x = -7
      rw [h]
      norm_num
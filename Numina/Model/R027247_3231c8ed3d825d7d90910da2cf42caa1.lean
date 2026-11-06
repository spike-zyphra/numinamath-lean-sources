import Mathlib

theorem algebra_233998 (u v w : ℝ) :
    u + v * w = 12 ∧ v + w * u = 12 ∧ w + u * v = 12 ↔
    (u = 3 ∧ v = 3 ∧ w = 3) ∨ (u = -4 ∧ v = -4 ∧ w = -4) ∨
    (u = 1 ∧ v = 1 ∧ w = 11) ∨ (u = 11 ∧ v = 1 ∧ w = 1) ∨
    (u = 1 ∧ v = 11 ∧ w = 1) := by 
  constructor
  · -- Assume the conjunction of equations holds, prove the disjunction of solutions.
    rintro ⟨h1, h2, h3⟩
    have h4 : (u - v) * (1 - w) = 0 := by 
      nlinarith
    cases (mul_eq_zero.mp h4) with
    | inl h4 =>
      have h5 : u = v := by linarith
      have h6 : w + u ^ 2 = 12 := by
        rw [show v = u by linarith [h5]] at h3
        nlinarith
      have h7 : u + u * w = 12 := by
        rw [show v = u by linarith [h5]] at h1
        linarith
      have h8 : (1 - u) * (w - u) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h8 =>
        have hu : u = 1 := by linarith
        have hv : v = 1 := by linarith [h5, hu]
        have hw : w = 11 := by
          rw [hu] at h7
          nlinarith
        simp [hu, hv, hw]
      | inr h8 =>
        have h9 : w = u := by linarith
        have h10 : u ^ 2 + u - 12 = 0 := by
          rw [h9] at h7
          nlinarith
        have h11 : (u - 3) * (u + 4) = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h11) with
        | inl h12 =>
          have hu : u = 3 := by linarith
          have hv : v = 3 := by linarith [h5, hu]
          have hw : w = 3 := by linarith [h9, hu]
          left
          exact ⟨hu, hv, hw⟩
        | inr h13 =>
          have hu : u = -4 := by linarith
          have hv : v = -4 := by linarith [h5, hu]
          have hw : w = -4 := by linarith [h9, hu]
          right
          left
          exact ⟨hu, hv, hw⟩
    | inr h4 =>
      have hw1 : w = 1 := by linarith
      have h8 : u + v = 12 := by
        rw [hw1] at h1
        nlinarith
      have h10 : u * v = 11 := by
        rw [hw1] at h3
        nlinarith
      have h11 : u ^ 2 - 12 * u + 11 = 0 := by
        have h12 : v = 12 - u := by linarith [h8]
        rw [h12] at h10
        nlinarith
      have h12 : (u - 11) * (u - 1) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h12) with
      | inl h13 =>
        have hu : u = 11 := by linarith
        have hv : v = 1 := by linarith [h8, hu]
        right
        right
        right
        left
        exact ⟨by linarith, by linarith, by linarith [hw1]⟩
      | inr h14 =>
        have hu : u = 1 := by linarith
        have hv : v = 11 := by linarith [h8, hu]
        right
        right
        right
        right
        exact ⟨by linarith, by linarith, by linarith [hw1]⟩
  · -- Assume the disjunction of solutions holds, prove the conjunction of equations.
    rintro (h | h | h | h | h)
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · rcases h with ⟨rfl, rfl, rfl⟩
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
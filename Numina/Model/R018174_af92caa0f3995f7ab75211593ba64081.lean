import Mathlib

theorem algebra_95347 (k : ℝ) :
    (∃ x : ℝ, 2*x^2-k*x+x+8=0 ∧ deriv (fun x => 2*x^2-k*x+x+8) x = 0) ↔
    k = 9 ∨ k = -7 := by
  constructor
  · -- Assume there exists such an x, prove k = 9 or k = -7
    rintro ⟨x, ⟨h_eq, h_deriv⟩⟩
    have h1 : deriv (fun x : ℝ => 2 * x^2 - k * x + x + 8) x = 4 * x + (1 - k) := by
      simp [deriv_pow, deriv_mul, deriv_id', mul_comm k x, add_assoc, sub_eq_add_neg]
      all_goals
      ring_nf
      <;> field_simp
      <;> ring
    rw [h1] at h_deriv
    have hk : k = 1 + 4 * x := by linarith 
    rw [hk] at h_eq
    have hx : x ^ 2 = 4 := by
      nlinarith
    have h2 : x = 2 ∨ x = -2 := by
      have h3 : (x - 2) * (x + 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h3) with
      | inl h4 =>
        left
        linarith
      | inr h5 =>
        right
        linarith
    cases h2 with
    | inl h2 =>
      -- x = 2, k = 9
      have hk2 : k = 9 := by
        rw [h2] at hk
        linarith
      left
      exact hk2
    | inr h2 =>
      -- x = -2, k = -7
      have hk2 : k = -7 := by
        rw [h2] at hk
        linarith
      right
      exact hk2
  · -- Assume k = 9 or k = -7, prove there exists such an x
    rintro (hk | hk)
    · -- k = 9
      use 2
      constructor
      · -- Show 2*x^2-k*x+x+8=0
        rw [hk]
        norm_num
      · -- Show deriv (fun x => 2*x^2-k*x+x+8) x = 0
        rw [hk]
        simp [deriv_pow, deriv_mul, deriv_id', mul_comm]
        all_goals
        norm_num
    · -- k = -7
      use -2
      constructor
      · -- Show 2*x^2-k*x+x+8=0
        rw [hk]
        norm_num
      · -- Show deriv (fun x => 2*x^2-k*x+x+8) x = 0
        rw [hk]
        simp [deriv_pow, deriv_mul, deriv_id', mul_comm]
        all_goals
        norm_num
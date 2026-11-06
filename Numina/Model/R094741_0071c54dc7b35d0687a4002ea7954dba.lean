import Mathlib

theorem algebra_199818 {x y z : ℝ} (h1 : x * y + x * z = 8 - x ^ 2) (h2 : x * y + y * z = 12 - y ^ 2)
    (h3 : y * z + z * x = -4 - z ^ 2) :
    (x = 2 ∧ y = 3 ∧ z = -1) ∨ (x = -2 ∧ y = -3 ∧ z = 1) := by
  have h4 : (x + y + z) ^ 2 = 16 := by
    nlinarith [h1, h2, h3]
  have h5 : x + y + z = 4 ∨ x + y + z = -4 := by
    have h : (x + y + z) ^ 2 = 16 := h4
    have h8 : (x + y + z) = 4 ∨ (x + y + z) = -4 := by
      have h9 : (x + y + z) ^ 2 - 16 = 0 := by linarith
      have h10 : (x + y + z - 4) * (x + y + z + 4) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h10) with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith
    exact h8
  cases h5 with
  | inl h5 =>
    have hx1 : x = 2 := by
      have eq1 : x * (y + z) = 8 - x ^ 2 := by
        nlinarith
      have yz : y + z = 4 - x := by linarith
      rw [yz] at eq1
      nlinarith [h5]
    have hy : y = 3 := by 
      rw [hx1] at h2
      have h6 : y + z = 2 := by
        nlinarith
      have h7 : 2 * y + y * z = 12 - y ^ 2 := by 
        nlinarith
      have hz1 : z = 2 - y := by linarith
      rw [hz1] at h7
      nlinarith
    have hz : z = -1 := by
      nlinarith [hy]
    left
    exact ⟨hx1, hy, hz⟩
  | inr h5 =>
    have hx2 : x = -2 := by
      have eq1 : x * (y + z) = 8 - x ^ 2 := by
        nlinarith
      have yz : y + z = -4 - x := by linarith
      rw [yz] at eq1
      nlinarith [h5]
    have hy2 : y = -3 := by 
      rw [hx2] at h2
      have h6 : y + z = -2 := by 
        nlinarith
      have h7 : -2 * y + y * z = 12 - y ^ 2 := by
        nlinarith
      have h8 : z = -2 - y := by linarith
      rw [h8] at h7
      nlinarith
    have hz2 : z = 1 := by
      nlinarith [hy2]
    right
    exact ⟨hx2, hy2, hz2⟩
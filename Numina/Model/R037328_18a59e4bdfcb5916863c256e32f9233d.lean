import Mathlib

theorem algebra_210021 (a b c : ℝ) (h : ¬(a = b ∧ b = c)) (x y z : ℝ)
    (hx : x = a^2 - b * c) (hy : y = b^2 - c * a) (hz : z = c^2 - a * b) :
    x > 0 ∨ y > 0 ∨ z > 0 := by
  by_contra h1
  push_neg at h1
  have h2 : x ≤ 0 := by linarith
  have h3 : y ≤ 0 := by linarith
  have h4 : z ≤ 0 := by linarith
  have h5 : x + y + z ≤ 0 := by linarith
  have h6 : x + y + z = 1 / 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
    rw [hx, hy, hz]
    ring
  have h7 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 0 := by
    by_contra h8
    push_neg at h8
    have h8' : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg
    have h8'' : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg
    have h8''' : (c - a) ^ 2 ≥ 0 := by apply sq_nonneg
    have h8'''' : (a - b) ^ 2 = 0 := by linarith [h8, h8', h8'', h8''']
    have h8''''' : a - b = 0 := by
      rw [sq_eq_zero_iff] at h8''''
      linarith
    have h8'''''' : (b - c) ^ 2 = 0 := by linarith [h8, h8', h8'', h8''']
    have h8''''''' : b - c = 0 := by
      rw [sq_eq_zero_iff] at h8''''''
      linarith
    have h8'''''''' : a = b := by linarith
    have h8''''''''' : b = c := by linarith
    have h9 : a = b ∧ b = c := ⟨h8'''''''', h8'''''''''⟩
    tauto
  -- Now, we can show that x + y + z > 0
  have h8 : x + y + z > 0 := by
    have h7' : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 > 0 := h7
    linarith [h6, h7']
  linarith
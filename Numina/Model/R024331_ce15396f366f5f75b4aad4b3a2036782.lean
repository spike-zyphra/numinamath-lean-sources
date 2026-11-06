import Mathlib

theorem algebra_314235 (x y z : ℕ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : z ^ y / y = y ^ (2 * x)) (h2 : 2 ^ z = 2 * 4 ^ x) (h3 : x + y + z = 12) :
    x = 2 ∧ y = 5 ∧ z = 5 := by

  have h4 : z = 1 + 2 * x := by
    have h5 : 2 ^ z = 2 * 4 ^ x := h2
    have h6 : 4 ^ x = 2 ^ (2 * x) := by
      rw [show 4 = 2 ^ 2 by norm_num]
      rw [← pow_mul]
    rw [h6] at h5
    have h7 : z = 1 + 2 * x := by
      have h8 : 2 ^ z = 2 ^ (1 + 2 * x) := by
        ring_nf at h5 ⊢
        all_goals omega
      have h9 : z = 1 + 2 * x := by
        exact Nat.pow_right_injective (by norm_num) h8
      exact h9
    exact h7

  have h8 : y = 11 - 3 * x := by
    have h9 : x + y + z = 12 := h3
    rw [show z = 1 + 2 * x by linarith [h4]] at h9
    omega

  have h10 : x ≤ 3 := by
    by_contra h
    push_neg at h
    have h11 : 3 * x ≥ 12 := by omega
    have h12 : y ≤ 0 := by omega
    have h13 : y > 0 := hy
    omega

  have h11 : x = 1 ∨ x = 2 ∨ x = 3 := by
    omega

  rcases h11 with (h | h | h)
  · -- Case x = 1
    have hx1 : x = 1 := h
    have hy1 : y = 8 := by
      omega
    have hz1 : z = 3 := by
      omega
    rw [hx1, hy1, hz1] at h1
    all_goals norm_num at h1
    all_goals linarith
  · -- Case x = 2
    have hx2 : x = 2 := h
    have hy2 : y = 5 := by
      omega
    have hz2 : z = 5 := by
      omega
    exact ⟨by linarith, by linarith, by linarith⟩
  · -- Case x = 3
    have hx3 : x = 3 := h
    have hy3 : y = 2 := by
      omega
    have hz3 : z = 7 := by
      omega
    rw [hx3, hy3, hz3] at h1
    all_goals norm_num at h1
    all_goals linarith
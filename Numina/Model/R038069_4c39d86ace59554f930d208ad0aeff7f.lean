import Mathlib

theorem algebra_2125 (m n k : ℝ) (h₀ : ¬∃ x, abs (2 * x - 3) + m = 0)
    (h₁ : ∃! x, abs (3 * x - 4) + n = 0) (h₂ : ∃ x y, x ≠ y ∧ abs (4 * x - 5) + k = 0 ∧
    abs (4 * y - 5) + k = 0) : m > n ∧ n > k := by
  have h3 : m > 0 := by
    by_contra h
    push_neg at h
    have h4 : ∃ x, abs (2 * x - 3) + m = 0 := by
      use (3 - m) / 2
      have h5 : abs (2 * ((3 - m) / 2) - 3) + m = 0 := by
        have h6 : abs (2 * ((3 - m) / 2) - 3) = abs (-m) := by
          ring_nf
        rw [h6]
        have h8 : abs (-m) = -m := by
          apply abs_of_nonneg
          linarith
        linarith
      linarith
    exact h₀ h4

  have h4 : n = 0 := by
    rcases h₁ with ⟨x, ⟨hx1, hx2⟩⟩
    have h_eq1 : abs (3 * x - 4) + n = 0 := hx1
    have h_eq2 : abs (3 * ((4 + (3 * x - 4) * (-1)) / 3) - 4) + n = 0 := by
      have h9 : abs (3 * ((4 + (3 * x - 4) * (-1)) / 3) - 4) = abs (3 * x - 4) := by
        have h10 : 3 * ((4 + (3 * x - 4) * (-1)) / 3) - 4 = -(3 * x - 4) := by
          ring_nf
        rw [h10]
        have h11 : abs (-(3 * x - 4)) = abs (3 * x - 4) := by
          rw [abs_neg]
        linarith
      linarith [h_eq1, h9]
    have h_eq3 : ((4 + (3 * x - 4) * (-1)) / 3) = x := by
      apply hx2
      linarith
    have h12 : x = 4 / 3 := by
      linarith
    rw [h12] at h_eq1
    have h13 : abs (3 * (4 / 3 : ℝ) - 4) = 0 := by
      norm_num
    have h14 : n = 0 := by
      linarith [h13, h_eq1]
    linarith

  have h5 : k < 0 := by
    rcases h₂ with ⟨x, y, hxy, hx, hy⟩
    by_contra h
    push_neg at h
    have h6 : abs (4 * x - 5) ≥ 0 := abs_nonneg (4 * x - 5)
    have h7 : abs (4 * y - 5) ≥ 0 := abs_nonneg (4 * y - 5)
    have heq1 : abs (4 * x - 5) = -k := by linarith
    have heq2 : abs (4 * y - 5) = -k := by linarith
    have hk1 : -k ≥ 0 := by linarith
    have hk0 : k = 0 := by linarith
    rw [hk0] at hx hy
    have hx0 : abs (4 * x - 5) = 0 := by linarith
    have hy0 : abs (4 * y - 5) = 0 := by linarith
    have h8 : 4 * x - 5 = 0 := by
      rwa [abs_eq_zero] at hx0
    have h9 : 4 * y - 5 = 0 := by
      rwa [abs_eq_zero] at hy0
    have h10 : x = y := by
      linarith
    contradiction

  have hm : m > n := by linarith [h3, h4]
  have hn : n > k := by linarith [h4, h5]
  constructor
  · exact hm
  · exact hn
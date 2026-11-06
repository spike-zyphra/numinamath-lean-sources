import Mathlib

theorem algebra_321395 (f : ℤ → ℤ) (h1 : f 1 = 1) (h2 : f 2 = 0)
    (h3 : ∀ x y, f (x + y) = f x * f (1 - y) + f (1 - x) * f y) :
    f 2015 = 1 ∨ f 2015 = -1 := by

  have h0 : f 0 = 0 := by
    have h4 : f (0 + 0) = f 0 * f (1 - 0) + f (1 - 0) * f 0 := h3 0 0
    simp [h1] at h4
    linarith

  have h4 : ∀ x, f (x + 1) = f (1 - x) := by
    intro x
    have h5 : f (x + 1) = f x * f (1 - 1) + f (1 - x) * f 1 := by
      specialize h3 x 1
      simpa using h3
    simp [h0, h1] at h5
    linarith

  have h5 : ∀ x, f (x + 2) = f x * f (-1) := by
    intro x
    have h7 : f (x + 2) = f x * f (1 - 2) + f (1 - x) * f 2 := by
      specialize h3 x 2
      simpa using h3
    have h8 : f (1 - 2) = f (-1) := by ring_nf
    rw [h8, h2] at h7
    simp at h7 ⊢
    all_goals linarith

  have h6 : f (-1) ^ 2 = 1 := by
    have h7 : f (2 + (-1)) = f 2 * f (1 - (-1)) + f (1 - 2) * f (-1) := h3 2 (-1)
    norm_num at h7
    all_goals
      nlinarith [h1, h2, h0]

  have h7 : f (-1) = 1 ∨ f (-1) = -1 := by
    have h8 : f (-1) ^ 2 = 1 := h6
    have : f (-1) = 1 ∨ f (-1) = -1 := by
      rw [sq_eq_one_iff] at h8
      tauto
    assumption

  rcases h7 with h7 | h7
  · -- If f(-1) = 1
    have h10 : ∀ x, f (x + 2) = f x := by
      intro x
      have h11 : f (x + 2) = f x * f (-1) := h5 x
      rw [show f (-1) = 1 by linarith [h7]] at h11
      linarith

    have h13 : f 2015 = f 1 := by
      have h14 : f 2015 = f (1 + 2 * 1007) := by norm_num
      rw [h14]
      have h17 : ∀ k : ℕ, f (1 + (2 * (k : ℤ))) = f 1 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          have h18 : (1 + (2 * ((k + 1 : ℕ) : ℤ)) : ℤ) = (1 + (2 * ((k : ℕ) : ℤ)) : ℤ) + 2 := by
            simp [mul_add, add_mul]
            all_goals omega
          rw [h18]
          have h19 : f ((1 + (2 * ((k : ℕ) : ℤ)) : ℤ) + 2) = f (1 + (2 * ((k : ℕ) : ℤ)) : ℤ) := by
            apply h10
          linarith [h19, ih]
      specialize h17 1007
      simpa using h17

    have h13' : f 1 = 1 := h1
    rw [h13'] at h13
    left
    linarith
  · -- If f(-1) = -1
    have h10 : ∀ x, f (x + 2) = - f x := by
      intro x
      have h11 : f (x + 2) = f x * f (-1) := h5 x
      rw [show f (-1) = -1 by linarith [h7]] at h11
      linarith

    have h13 : f 2015 = f 3 := by
      have h14 : f 2015 = f (3 + 4 * 503) := by norm_num
      rw [h14]
      have h17 : ∀ k : ℕ, f (3 + (4 * (k : ℤ)) ) = f 3 := by
        intro k
        induction k with
        | zero =>
          norm_num
        | succ k ih =>
          have h18 : (3 + (4 * ((k + 1 : ℕ) : ℤ)) : ℤ) = (3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 4 := by
            simp [mul_add, add_mul]
            all_goals omega
          rw [h18]
          have h20 : f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 4) = f (3 + (4 * ((k : ℕ) : ℤ)) : ℤ) := by
            have h21 : f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 2) = - f (3 + (4 * ((k : ℕ) : ℤ)) : ℤ) := by
              apply h10
            have h25 : f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 4) = - f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 2) := by
              have h100 : f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 2 + 2) = - f ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 2) := by
                specialize h10 ((3 + (4 * ((k : ℕ) : ℤ)) : ℤ) + 2)
                linarith [h10]
              ring_nf at h100 ⊢
              all_goals linarith
            linarith [h25, h21]
          linarith [h20, ih]
      specialize h17 503
      simpa using h17

    have h18 : f 3 = -1 := by
      have h19 : f 3 = f 1 * f (1 - (2 : ℤ)) + f (1 - 1) * f (2 : ℤ) := by
        have h20 : f (1 + 2) = f 1 * f (1 - (2 : ℤ)) + f (1 - 1) * f (2 : ℤ) := by
          apply h3
        norm_num at h20 ⊢
        linarith
      have h20 : f 1 = 1 := h1
      have h21 : f (1 - (2 : ℤ)) = f (-1) := by ring_nf
      have h22 : f (1 - 1) = f 0 := by ring_nf
      have h23 : f 0 = 0 := h0
      have h24 : f 2 = 0 := h2
      have h25 : f (-1) = -1 := by linarith [h7]
      rw [h20, h21, h22, h23, h24, h25] at h19
      linarith

    rw [h18] at h13
    right
    linarith
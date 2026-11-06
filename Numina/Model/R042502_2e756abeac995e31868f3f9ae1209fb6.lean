import Mathlib

theorem algebra_155581 {x : ℝ} (hx : ⌊x⌋ = (8 / 9) * (x - 4) + 3) (h : x - ⌊x⌋ = (1 / 9) * (x + 5)) :
    ∃ k : ℕ, k ∈ Finset.Icc 1 8 ∧ x = -5 + ((9 / 8) * (k - 1)) := by
  let n := ⌊x⌋
  have h1 : (n : ℝ) = (8 / 9) * (x - 4) + 3 := by simpa using hx
  have h2 : x - (n : ℝ) = (1 / 9) * (x + 5) := by simpa using h

  have eq1 : (n : ℝ) = (8 / 9) * x - 5 / 9 := by
    nlinarith [h1, h2]

  have eq2 : x = (9 / 8) * (n : ℝ) + 5 / 8 := by
    nlinarith [eq1]

  have h3 : (n : ℝ) ≤ x := by exact_mod_cast (Int.floor_le x)
  have h4 : x < (n + 1 : ℝ) := by exact_mod_cast (Int.lt_floor_add_one x)

  rw [eq2] at h3 h4
  have h5 : n ≥ -5 := by
    by_contra h5
    push_neg at h5
    have h6 : n < -5 := by omega
    have hn : (n : ℝ) ≤ (-6 : ℝ) := by exact_mod_cast (show (n : Int) ≤ -6 from by omega)
    nlinarith

  have h6 : n < 3 := by
    by_contra h6
    push_neg at h6
    have h7 : n ≥ 3 := by omega
    have hn : (n : ℝ) ≥ (3 : ℝ) := by exact_mod_cast (show (n : Int) ≥ 3 from by omega)
    nlinarith

  have h7 : n = -5 ∨ n = -4 ∨ n = -3 ∨ n = -2 ∨ n = -1 ∨ n = 0 ∨ n = 1 ∨ n = 2 := by
    omega

  rcases h7 with (hn | hn | hn | hn | hn | hn | hn | hn)
  · -- Case n = -5, so x = -5
    use 1
    constructor
    · -- Show that 1 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(1 - 1)
      have h9 : (n : ℝ) = (-5 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (-5 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = -4, so x = -3.875
    use 2
    constructor
    · -- Show that 2 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(2 - 1)
      have h9 : (n : ℝ) = (-4 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (-4 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = -3, so x = -2.75
    use 3
    constructor
    · -- Show that 3 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(3 - 1)
      have h9 : (n : ℝ) = (-3 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (-3 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = -2, so x = -1.625
    use 4
    constructor
    · -- Show that 4 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(4 - 1)
      have h9 : (n : ℝ) = (-2 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (-2 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = -1, so x = -0.5
    use 5
    constructor
    · -- Show that 5 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(5 - 1)
      have h9 : (n : ℝ) = (-1 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (-1 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = 0, so x = 0.625
    use 6
    constructor
    · -- Show that 6 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(6 - 1)
      have h9 : (n : ℝ) = (0 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (0 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = 1, so x = 1.75
    use 7
    constructor
    · -- Show that 7 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(7 - 1)
      have h9 : (n : ℝ) = (1 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (1 : ℝ) from h9] at eq2
      linarith [eq2, h9]
  · -- Case n = 2, so x = 2.875
    use 8
    constructor
    · -- Show that 8 ∈ [1, 8]
      simp [Finset.mem_Icc]
    · -- Show x = -5 + 9/8*(8 - 1)
      have h9 : (n : ℝ) = (2 : ℝ) := by rw [hn]; norm_num
      rw [show (n : ℝ) = (2 : ℝ) from h9] at eq2
      linarith [eq2, h9]
import Mathlib

theorem algebra_321867 (a : ℕ → ℝ) (ha : a 1 = 32) (h : ∀ n > 0, a (n + 1) - a n = 2 * n) :
    IsLeast {x | ∃ n > 0, x = a n / n} (31 / 3) := by

  have ha2 : a 2 = 34 := by
    have eq1 : a 2 - a 1 = 2 * (1 : ℕ) := h 1 (by norm_num)
    rw [ha] at eq1
    norm_num at eq1 ⊢
    linarith
  have ha3 : a 3 = 38 := by
    have eq1 : a 3 - a 2 = 2 * (2 : ℕ) := h 2 (by norm_num)
    rw [ha2] at eq1
    norm_num at eq1 ⊢
    linarith
  have ha4 : a 4 = 44 := by
    have eq1 : a 4 - a 3 = 2 * (3 : ℕ) := h 3 (by norm_num)
    rw [ha3] at eq1
    norm_num at eq1 ⊢
    linarith
  have ha5 : a 5 = 52 := by
    have eq1 : a 5 - a 4 = 2 * (4 : ℕ) := h 4 (by norm_num)
    rw [ha4] at eq1
    norm_num at eq1 ⊢
    linarith
  have ha6 : a 6 = 62 := by
    have eq1 : a 6 - a 5 = 2 * (5 : ℕ) := h 5 (by norm_num)
    rw [ha5] at eq1
    norm_num at eq1 ⊢
    linarith
  constructor
  · -- Show $\frac{31}{3}$ is achievable, at n = 6.
    use 6
    constructor
    · norm_num
    · -- Show that with n = 6, a 6 /6 = 31/3.
      rw [ha6]
      norm_num
  · -- Show no smaller value is achieved.
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    by_contra h'
    push_neg at h'
    have h1 : a n / (n : ℝ) < (31 / 3) := by
      linarith [h', hx]
    have h2 : ∀ n : ℕ, n > 0 → a n = (n : ℝ) ^ 2 - (n : ℝ) + 32 := by
      intro n hn
      induction n with
      | zero =>
        exfalso
        linarith
      | succ n ih =>
        cases n with
        | zero =>
          rw [ha]
          norm_num
        | succ n =>
          have eq1 : a (n + 1 + 1) - a (n + 1) = 2 * (n + 1 : ℕ) := h (n + 1) (by linarith)
          have h3 : a (n + 2) = a (n + 1) + 2 * (n + 1 : ℝ) := by
            simp [show n + 1 + 1 = n + 2 by omega] at eq1 ⊢
            linarith
          rw [h3]
          rw [ih (by linarith)]
          field_simp
          ring
    have h3 : a n / (n : ℝ) < (31 / 3) := h1
    have h1' : a n = (n : ℝ) ^ 2 - (n : ℝ) + 32 := h2 n (by linarith)
    rw [h1'] at h3
    have h4 : (n : ℝ) > 0 := by exact_mod_cast (show (n : ℕ) > 0 by linarith)
    by_cases h5 : n ≤ 5
    · -- If n ≤ 5
      have h6 : n ≤ 5 := h5
      have h7 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by
        have h8 : n > 0 := by linarith
        interval_cases n <;> omega
      rcases h7 with (rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        norm_num [ha] at h3
      · -- n = 2
        norm_num [ha2] at h3
      · -- n = 3
        norm_num [ha3] at h3
      · -- n = 4
        norm_num [ha4] at h3
      · -- n = 5
        norm_num [ha5] at h3
    · -- If n > 5
      push_neg at h5
      have h8 : n ≥ 6 := by
        omega
      have h9 : (n : ℝ) ≥ 6 := by
        exact_mod_cast h8
      have h5' : ( (n : ℝ) ^ 2 - (n : ℝ) + 32 ) / ( (n : ℝ) ) ≥ (31 / 3 : ℝ) := by
        have hn1 : (n : ℝ) ≥ (6 : ℝ) := by
          exact_mod_cast h8
        have h10 : (n : ℝ) ^ 2 - (n : ℝ) + 32 ≥ (31 / 3 : ℝ) * (n : ℝ) := by
          nlinarith [sq_nonneg ( (n : ℝ) - (6 : ℝ) ), sq_nonneg ( (n : ℝ) - (5 : ℝ) ) ]
        apply (le_div_iff₀ (by positivity : (n : ℝ) > 0)).mpr
        linarith
      linarith
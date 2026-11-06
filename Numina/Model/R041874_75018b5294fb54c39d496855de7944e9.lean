import Mathlib

theorem number_theory_36588 {b : ℕ → ℝ} (hb : ∃ r, ∀ n, b n = b 1 * r ^ (n - 1))
    (h : ∃ a d, ∀ n, b n = a + d * n) (hb1 : ∃ m : ℤ, b 1 = m) :
    ∀ n, ∃ m : ℤ, b n = m := by
  rcases hb with ⟨r, hrr⟩
  rcases h with ⟨a, d, hab⟩
  rcases hb1 with ⟨m, hm⟩
  have eq1 := hab 1
  have eq2 := hab 2
  have eq3 := hab 3
  simp at eq1 eq2 eq3
  -- Simplify equations from hrr
  have eq11 := hrr 1
  have eq12 := hrr 2
  have eq13 := hrr 3
  simp at eq11 eq12 eq13
  have eq5 : r = 1 ∨ b 1 = 0 := by
    by_cases h1 : b 1 = 0
    · -- Case b 1 = 0
      right
      exact h1
    · -- Case b 1 ≠ 0
      left
      have eq7 : b 1 * r = a + 2 * d := by
        have h2 : b 2 = a + (2 * d) := by
          linarith [eq2]
        have h3 : b 2 = b 1 * r := by
          linarith [eq12]
        linarith
      have eq8 : b 1 * r ^ 2 = a + 3 * d := by
        have h4 : b 3 = a + (3 * d) := by
          linarith [eq3]
        have h5 : b 3 = b 1 * r ^ 2 := by
          linarith [eq13]
        linarith
      have eq9 : a = b 1 - d := by
        linarith [eq1]
      have eq22 : d = b 1 * (r - 1) := by
        have eq7' : b 1 * r = a + 2 * d := by linarith
        rw [show a = b 1 - d by linarith [eq9]] at eq7'
        have eq21 : d = b 1 * (r - 1) := by
          nlinarith
        exact eq21
      have eq23 : b 1 * r ^ 2 = b 1 + 2 * d := by
        have eq8' : b 1 * r ^ 2 = a + 3 * d := by linarith
        have eq7' : a = b 1 - d := by linarith [eq9]
        rw [eq7'] at eq8'
        linarith
      rw [show d = b 1 * (r - 1) by linarith [eq22]] at eq23
      have eq24 : (r - 1) ^ 2 = 0 := by
        apply (mul_left_inj' h1).mp
        linarith
      have eq25 : r = 1 := by
        nlinarith
      exact eq25
  cases eq5 with
  | inl h11 =>
    intro n
    have eq111 : b n = b 1 := by
      rw [hrr n]
      rw [h11]
      norm_num
      <;> ring_nf
    refine ⟨m, by simp [eq111, hm]⟩
  | inr h11 =>
    intro n
    have eq11 : b n = (0 : ℝ) := by
      have eq12 : b n = b 1 * r ^ (n - 1) := hrr n
      rw [eq12]
      rw [show b 1 = 0 by linarith [h11] ]
      norm_num
      <;> ring_nf
    refine ⟨(0 : ℤ), by simp [eq11]⟩
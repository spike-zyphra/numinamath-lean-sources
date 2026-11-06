import Mathlib

theorem algebra_244606 (m n p : ℤ) (hm : m > 0) (hn : n > 0) (hp : p > 0)
    (h : 3 * m + 3 / (n + 1 / p : ℚ) = 17) : p = 2 := by
  have h1 : (m : ℚ) > 0 := by exact_mod_cast hm
  have h2 : (n : ℚ) > 0 := by exact_mod_cast hn
  have h3 : (p : ℚ) > 0 := by exact_mod_cast hp
  have eq1 : 3 * (m : ℚ) + 3 / (n + (1 / (p : ℚ)) : ℚ) = (17 : ℚ) := by
    exact_mod_cast h
  have h_eq : (n : ℚ) + (1 / (p : ℚ) : ℚ) = ((n : ℚ) * (p : ℚ) + 1) / (p : ℚ) := by
    field_simp
    <;> ring
  rw [h_eq] at eq1
  have eq2 : 3 * (m : ℚ) * (n * (p : ℚ) + 1) + 3 * (p : ℚ) = 17 * ((n * (p : ℚ) + 1) : ℚ) := by
    have h' : (n * (p : ℚ) + 1 : ℚ) ≠ 0 := by
      norm_num
      all_goals 
        nlinarith [show 0 < (n : ℚ) from by exact_mod_cast hn, 
          show 0 < (p : ℚ) from by exact_mod_cast hp]
    field_simp [h'] at eq1 ⊢
    <;> norm_num at eq1 ⊢ <;> 
      nlinarith
  have eq3 : 3 * (m) * (n * (p : ℤ) + 1) + 3 * (p : ℤ) = 17 * ((n * (p : ℤ) + 1) : ℤ) := by
    exact_mod_cast eq2
  have bound2 : m < 6 := by
    have bound : (3 * (m : ℚ)) < (17 : ℚ) := by 
      have part1 : (3 / ((n * (p : ℚ) + 1) / (p : ℚ)) : ℚ) > 0 := by positivity
      linarith [eq1, part1]
    have bound3 : (m : ℚ) < (17 : ℚ) / 3 := by linarith
    have bound4 : m < 6 := by
      have bound5 : (m : ℚ) < (6 : ℚ) := by linarith
      exact_mod_cast bound5
      all_goals linarith
    linarith [bound4]
  have eq5 : m ≥ 1 := by linarith [hm]
  have eq6 : n ≥ 1 := by linarith [hn]
  have eq7 : p ≥ 1 := by linarith [hp]
  have m_cases : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 := by
    omega
  rcases m_cases with (rfl | rfl | rfl | rfl | rfl)
  · -- Case m = 1
    ring_nf at eq3
    norm_num at eq3
    have h8 : n = 1 := by
      nlinarith [eq3, show n ≥ 1 by linarith, show p ≥ 1 by linarith]
    rw [show n = 1 by linarith [h8]] at eq3
    have h9 : p = 2 := by
      nlinarith [eq3]
    exact h9
  · -- Case m = 2
    ring_nf at eq3
    norm_num at eq3
    have h8 : n = 1 := by
      nlinarith [eq3, show n ≥ 1 by linarith, show p ≥ 1 by linarith]
    rw [show n = 1 by linarith [h8]] at eq3
    have h9 : p = 2 := by
      nlinarith [eq3]
    exact h9
  · -- Case m = 3
    ring_nf at eq3
    norm_num at eq3
    have h8 : n = 1 := by
      nlinarith [eq3, show n ≥ 1 by linarith, show p ≥ 1 by linarith]
    rw [show n = 1 by linarith [h8]] at eq3
    have h9 : p = 2 := by
      nlinarith [eq3]
    exact h9
  · -- Case m = 4
    ring_nf at eq3
    norm_num at eq3
    have h8 : n = 1 := by
      nlinarith [eq3, show n ≥ 1 by linarith, show p ≥ 1 by linarith]
    rw [show n = 1 by linarith [h8]] at eq3
    have h9 : p = 2 := by
      nlinarith [eq3]
    exact h9
  · -- Case m = 5
    ring_nf at eq3
    norm_num at eq3
    have h8 : n = 1 := by
      nlinarith [eq3, show n ≥ 1 by linarith, show p ≥ 1 by linarith]
    rw [show n = 1 by linarith [h8]] at eq3
    have h9 : p = 2 := by
      nlinarith [eq3]
    exact h9
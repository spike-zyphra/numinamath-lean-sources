import Mathlib

/- A rectangle has integer side lengths. One pair of opposite sides is increased by $30\%$ and the other pair of sides is decreased by $20\%$. The new side lengths are also integers. What is the smallest possible area, in square units, of the new rectangle? -/
theorem number_theory_18713 :
    IsLeast {x | ∃ a b n m : ℕ, a > 0 ∧ b > 0 ∧ n = a * (1 + 30 / 100 : ℝ) ∧ m = b * (1 - 20 / 100 : ℝ) ∧ x = n * m} 52 := by
    constructor
    -- Show that $52$ is in the set
    use 10, 5, 13, 4
    norm_num
    -- Show that 52 is the least element
    intros y hy
    rcases hy with ⟨a, b, n, m, ha, hb, hn, hm, hy⟩
    -- Show that $13 \leq n$
    have ha' : 13 ≤ n := by
      norm_num at hn
      field_simp at hn
      have mid1 : n * (10 : ℝ) = (n * 10 : ℤ) := by
        norm_num
      have mid2 : a * (13 : ℝ) = (a * 13 : ℤ) := by 
        norm_num
      rw [mid1, mid2] at hn
      apply Int.cast_injective at hn
      have div : (10 : ℤ) ∣ a * 13 := by
        exact Dvd.intro_left n hn
      -- Show that $10 \mid a$, so $a \geq 10$
      have h1 : (10 : ℤ) ∣ a := by
        exact Int.dvd_of_dvd_mul_left_of_gcd_one div rfl
      norm_num
      apply Int.le_of_dvd at h1
      linarith
      exact Int.ofNat_pos.mpr ha
    -- Show that $4 \leq m$
    have hb' : 4 ≤ m := by
      norm_num at hm
      field_simp at hm
      have mid1 : m * (5 : ℝ) = (m * 5 : ℤ) := by
        norm_num
      have mid2 : b * (4 : ℝ) = (b * 4 : ℤ) := by 
        norm_num
      rw [mid1, mid2] at hm
      apply Int.cast_injective at hm
      have div : (5 : ℤ) ∣ b * 4 := by
        exact Dvd.intro_left m hm
      -- Show that $5 \mid b$, so $b \geq 5$
      have h1 : (5 : ℤ) ∣ b := by
        exact Int.dvd_of_dvd_mul_left_of_gcd_one div rfl
      norm_num
      apply Int.le_of_dvd at h1
      linarith
      exact Int.ofNat_pos.mpr hb
    -- Show that $52 \leq y$
    show 13 * 4 ≤ y
    rw [hy]
    exact Nat.mul_le_mul ha' hb'


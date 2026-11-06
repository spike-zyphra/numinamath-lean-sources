import Mathlib

theorem algebra_788 (m : ℤ) (x y : ℤ)
    (h₁ : 4 * x - 3 * y = 6) (h₂ : 6 * x + m * y = 26) :
    m = -4 ∨ m = -5 ∨ m = 4 ∨ m = -13 := by
  have h3 : y % 4 = 2 := by 
    omega
  have eq2 : ∃ k : ℤ, y = 4 * k + 2 := by
    have : y % 4 = 2 := h3
    refine' ⟨y / 4, by omega⟩
  rcases eq2 with ⟨k, hy⟩
  have hx : x = 3 * k + 3 := by
    rw [hy] at h₁
    omega
  rw [hx, hy] at h₂
  have eq3 : k * (9 + 2 * m) + m = 4 := by 
    linarith
  have h4 : (9 + 2 * m) ∣ (4 - m) := by
    use k
    linarith
  have h5 : (9 + 2 * m) ∣ 17 := by
    have h6 : (9 + 2 * m) ∣ (4 - m) := h4
    have h7 : (9 + 2 * m) ∣ (1 * (9 + 2 * m) + 2 * (4 - m)) := by
      apply Dvd.dvd.add
      · -- Show that (9 + 2 * m) ∣ 1 * (9 + 2 * m)
        simp
      · -- Show that (9 + 2 * m) ∣ 2 * (4 - m)
        apply dvd_trans h6
        simp
    have h11 : (1 * (9 + 2 * m) + 2 * (4 - m)) = 17 := by
      ring
    rw [h11] at h7
    exact h7
  have h9 : (9 + 2 * m) = 1 ∨ (9 + 2 * m) = 17 ∨ (9 + 2 * m) = -1 ∨ (9 + 2 * m) = -17 := by
    have h4 : (9 + 2 * m) ∣ 17 := h5
    have h5 : (9 + 2 * m) ≤ 17 := by
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : (9 + 2 * m) ≥ -17 := by 
      have h7 : (- (9 + 2 * m)) ∣ 17 := by
        exact Int.neg_dvd.2 h4
      have h8 : - (9 + 2 * m) ≤ 17 := by
        apply Int.le_of_dvd (by norm_num) h7
      omega
    interval_cases (9 + 2 * m) <;> try { tauto }
  rcases h9 with h9 | h9 | h9 | h9
  · -- Case 1: 9 + 2m = 1
    have h10 : 2 * m = -8 := by
      linarith
    have h11 : m = -4 := by
      linarith
    left
    exact h11
  · -- Case 2: 9 + 2m = 17
    have h12 : 2 * m = 8 := by 
      linarith
    have h13 : m = 4 := by
      linarith
    right
    right
    left
    exact h13
  · -- Case 3: 9 + 2m = -1
    have h14 : 2 * m = -10 := by 
      linarith
    have h15 : m = -5 := by 
      linarith
    right
    left
    exact h15
  · -- Case 4: 9 + 2m = -17
    have h16 : 2 * m = -26 := by 
      linarith
    have h17 : m = -13 := by 
      linarith
    right
    right
    right
    exact h17
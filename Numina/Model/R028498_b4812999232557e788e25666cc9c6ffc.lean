import Mathlib.Tactic
import Mathlib.Util.Delaborators

theorem AMC_Algebra_1196 (a b : Int) (area : 2*(a-2)*(b-2) - a*b = 0) (apos : a > 0) (bpos : b > 0) (hab : b > a) : (a = 5 ∧ b = 12) ∨ (a = 6 ∧ b = 8) := by
  have h1 : (a - 4) * (b - 4) = 8 := by
    nlinarith
  have h2 : a - 4 ∣ 8 := by
    use b - 4
    all_goals linarith
  have h3 : a - 4 ≤ 8 := by
    apply Int.le_of_dvd (by norm_num) h2
  have h4 : a - 4 ≥ -8 := by
    have h5 : (- (a - 4)) ∣ 8 := by
      exact Int.neg_dvd.2 h2
    have h6 : - (a - 4) ≤ 8 := by
      apply Int.le_of_dvd (by norm_num) h5
    omega
  have h5 : a - 4 = 1 ∨ a - 4 = 2 ∨ a - 4 = 4 ∨ a - 4 = 8 ∨
          a - 4 = -1 ∨ a - 4 = -2 ∨ a - 4 = -4 ∨ a - 4 = -8 := by
    interval_cases h : a - 4 <;> omega
  rcases h5 with (h | h | h | h | h | h | h | h)
  · -- Case a - 4 = 1, so a = 5, then b - 4 = 8, so b = 12
    have ha : a = 5 := by linarith
    have hb : b = 12 := by
      have h12 : a - 4 = 1 := by linarith
      have h12b : b - 4 = 8 := by
        rw [h12] at h1
        linarith
      linarith
    left
    exact ⟨ha, hb⟩
  · -- Case a - 4 = 2, so a = 6, then b - 4 = 4, so b = 8
    have ha : a = 6 := by linarith
    have hb : b = 8 := by
      have h12 : a - 4 = 2 := by linarith
      have h12b : b - 4 = 4 := by
        rw [h12] at h1
        linarith
      linarith
    right
    exact ⟨ha, hb⟩
  · -- Case a - 4 = 4, so a = 8, then b - 4 = 2, so b = 6
    exfalso
    have ha : a = 8 := by linarith
    have hb : b = 6 := by
      have h12 : a - 4 = 4 := by linarith
      have h12b : b - 4 = 2 := by
        rw [h12] at h1
        linarith
      linarith
    nlinarith
  · -- Case a - 4 = 8, so a = 12, then b - 4 = 1, so b = 5
    exfalso
    have ha : a = 12 := by linarith
    have hb : b = 5 := by
      have h12 : a - 4 = 8 := by linarith
      have h12b : b - 4 = 1 := by
        rw [h12] at h1
        linarith
      linarith
    nlinarith
  · -- Case a - 4 = -1, so a = 3, then b - 4 = -8, so b = -4
    exfalso
    have ha : a = 3 := by linarith
    have hb : b = -4 := by
      have h12 : a - 4 = -1 := by linarith
      have h12b : b - 4 = -8 := by
        rw [h12] at h1
        linarith
      linarith
    nlinarith
  · -- Case a - 4 = -2, so a = 2, then b - 4 = -4, so b = 0
    exfalso
    have ha : a = 2 := by linarith
    have hb : b = 0 := by
      have h12 : a - 4 = -2 := by linarith
      have h12b : b - 4 = -4 := by
        rw [h12] at h1
        linarith
      linarith
    nlinarith
  · -- Case a - 4 = -4, so a = 0, then b - 4 = -2, so b = 2
    exfalso
    have ha : a = 0 := by linarith
    have hb : b = 2 := by
      have h12 : a - 4 = -4 := by linarith
      have h12b : b - 4 = -2 := by
        rw [h12] at h1
        linarith
      linarith
    omega
  · -- Case a - 4 = -8, so a = -4, then b - 4 = -1, so b = 3
    exfalso
    have ha : a = -4 := by linarith
    have hb : b = 3 := by
      have h12 : a - 4 = -8 := by linarith
      have h12b : b - 4 = -1 := by
        rw [h12] at h1
        linarith
      linarith
    omega
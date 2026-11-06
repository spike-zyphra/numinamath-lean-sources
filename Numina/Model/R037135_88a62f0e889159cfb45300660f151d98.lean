import Mathlib

theorem algebra_2162 {m : ℤ} (hm : m > 0) (h : ∃ x y : ℤ, m * x + 2 * y = 10 ∧ 3 * x - 2 * y = 0) :
    m ^ 2 = 4 := by 
  rcases h with ⟨x, y, h1, h2⟩
  have h3 : 3 * x = 2 * y := by 
    omega
  have h4 : x % 2 = 0 := by 
    omega
  obtain ⟨k, hk⟩ : ∃ k, x = 2 * k := ⟨x / 2, by omega⟩
  have hy : y = 3 * k := by 
    rw [show x = 2 * k by linarith [hk]] at h3
    omega
  rw [show x = 2 * k by omega, show y = 3 * k by omega] at h1
  have h7 : m * (2 * k) + 2 * (3 * k) = 10 := by linarith [h1]
  have h8 : m * k + 3 * k = 5 := by
    nlinarith 
  have h9 : k * (m + 3) = 5 := by
    linarith 
  have h10 : k ∣ 5 := by 
    use m + 3 
    linarith 
  have h11 : k = 1 ∨ k = -1 ∨ k = 5 ∨ k = -5 := by 
    have h6 : k ∣ 5 := h10 
    have : k = 1 ∨ k = -1 ∨ k = 5 ∨ k = -5 := by 
      have h7 : k ≤ 5 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      have h8 : -5 ≤ k := by
        have h9 : -k ∣ 5 := by 
          exact Int.neg_dvd.2 h6 
        have h10 : -k ≤ 5 := by 
          apply Int.le_of_dvd (by norm_num) h9 
        omega 
      interval_cases k <;> tauto 
    tauto 
  rcases h11 with (h | h | h | h) 
  · -- k = 1 
    rw [h] at h9 
    have hm3 : m + 3 = 5 := by 
      nlinarith 
    have hm2 : m = 2 := by 
      omega 
    rw [hm2] 
    all_goals nlinarith 
  · -- k = -1 
    rw [h] at h9 
    -- -1 * (m + 3) = 5 
    -- -m - 3 = 5 
    -- -m = 8 
    -- m = -8
    -- Contradicts with hm > 0
    nlinarith 
  · -- k = 5 
    rw [h] at h9 
    -- 5 * (m + 3) = 5
    -- m + 3 = 1 
    -- m = -2
    -- Contradicts with hm > 0
    -- m = -2
    nlinarith 
  · -- k = -5 
    rw [h] at h9 
    -- -5 * (m + 3) = 5 
    -- m + 3 = -1 
    -- m = -4 
    -- Contradicts with hm > 0
    nlinarith
import Mathlib

theorem algebra_7281 :
    IsGreatest {x : ℚ | ∃ n m : ℤ, 39 < n ∧ n < 81 ∧ 19 < m ∧ m < 41 ∧ x = (n / m : ℚ) + (m / n : ℚ)} (17 / 4) := by
  constructor
  · -- Show that 17/4 is in the set
    use 80, 20
    norm_num
  · -- Show that it is greatest
    intro x hx
    rcases hx with ⟨n, m, hn1, hn2, hm1, hm2, h_eq⟩
    have eq : (n / m : ℚ) + (m / n : ℚ) = (n^2 + m^2 : ℚ) / (n * m) := by
      field_simp
      <;> ring
    have eq' : x = (n^2 + m^2 : ℚ) / (n * m) := by 
      rw [h_eq]
      rw [eq]
    have hn3 : n > 0 := by linarith
    have hm3 : m > 0 := by linarith
    have h1 : (n * m : ℤ) > 0 := mul_pos hn3 hm3
    have h2 : (n^2 + m^2 : ℚ) / (n * m) ≤ 17 / 4 := by
      have h4 : 0 < (n * m : ℚ) := by positivity
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h5 : (n^2 + m^2 : ℚ) * 4 ≤ 17 * (n * m : ℚ) := by
        have h6 : (n : ℤ) ≥ 40 := by linarith
        have h7 : (n : ℤ) ≤ 80 := by linarith
        have h8 : (m : ℤ) ≥ 20 := by linarith
        have h9 : (m : ℤ) ≤ 40 := by linarith
        have h10 : (n : ℤ) ≤ 80 := by linarith
        have h11 : (m : ℤ) ≤ 40 := by linarith
        interval_cases n <;> interval_cases m <;> norm_num at *
        <;> linarith
      linarith
    rw [eq']
    linarith
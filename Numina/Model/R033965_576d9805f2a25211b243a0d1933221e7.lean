import Mathlib

theorem algebra_115351 {k p : ℕ} (hk : 0 < k) (hroots : ∃ m n, m ≠ n ∧ m > 0 ∧ n > 0 ∧ (k - 1) * m ^ 2 - p * m + k = 0 ∧ (k - 1) * n ^ 2 - p * n + k = 0) :
    k ^ (k * p) * (p ^ p + k ^ k) = 1984 := by

  rcases hroots with ⟨m, n, h1, hm, hn, h2, h3⟩
  have h4 : (k - 1) * m ^ 2 + k = p * m := by 
    omega

  have h5 : (k - 1) * n ^ 2 + k = p * n := by 
    omega
  
  have h6 : k = 2 := by
    have eq1 : (k - 1) * (m ^ 2 - n ^ 2) = p * (m - n) := by 
      omega

    have eq2 : (k - 1) * (m + n) = p := by
      have h1' : m ≠ n := h1
      have h2' : m - n ≠ 0 := by
        omega
      apply (mul_left_inj' (show m - n ≠ 0 by omega)).mp
      nlinarith
  
    nlinarith [sq_pos_of_pos (show 0 < m by linarith), sq_pos_of_pos (show 0 < n by linarith), 
      mul_pos (show 0 < m by linarith) (show 0 < n by linarith), 
      sq_nonneg (m - n), sq_pos_of_pos hk]

  have h7 : p = 3 := by
    have eq2 : (k - 1) * (m + n) = p := by 
      have h1' : m ≠ n := h1
      have h2' : m - n ≠ 0 := by 
        omega
      apply (mul_left_inj' (show m - n ≠ 0 by omega)).mp
      nlinarith
    rw [h6] at eq2 
    nlinarith [h1, sq_pos_of_pos (show 0 < m by linarith), sq_pos_of_pos (show 0 < n by linarith), 
      mul_pos (show 0 < m by linarith) (show 0 < n by linarith), sq_nonneg (m - n)]
  
  rw [h6, h7]
  all_goals
    norm_num
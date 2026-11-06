import Mathlib
theorem algebra_622370 {a b k m n : ℝ}
    (ha : 0 < a) (hb : a < b)  -- Given: 0 < a < b
    (hk : 0 < k) (hm : 0 < m) (hn : 0 < n)  -- All variables positive
    -- Geometric progression condition: a, k, b form geometric sequence
    (hge : ∃ r, a * r = k ∧ k * r = b)
    -- Arithmetic progression condition: a, m, n, b form arithmetic sequence
    (har : ∃ d, a + d = m ∧ m + d = n ∧ n + d = b) :
    -- Goal: Prove this inequality holds under given conditions
    (k + 1)^2 < (m + 1) * (n + 1) := by
  rcases hge with ⟨r, h1, h2⟩
  rcases har with ⟨d, h3, h4, h5⟩
  have h6 : k = a * r := by linarith
  have h7 : b = a * r^2 := by
    have h8 : k * r = b := by linarith
    rw [h6] at h8
    nlinarith 
  have h8 : m = a + d := by linarith 
  have h9 : n = m + d := by linarith
  have h10 : b = n + d := by linarith
  have h11 : n = a + 2 * d := by
    nlinarith [h8, h9]
  have h12 : b = a + 3 * d := by
    nlinarith [h11, h10]
  have h13 : d = (b - a) / 3 := by
    nlinarith
  have h14 : m = (2 * a + b) / 3 := by 
    nlinarith [h8, h13]
  have h15 : n = (a + 2 * b) / 3 := by 
    nlinarith [h11, h13]
  have h18 : k ^ 2 = a * b := by
    have h19 : k = a * r := by linarith
    have h20 : b = a * r^2 := by 
      nlinarith 
    have h21 : k^2 = (a * r) ^ 2 := by
      rw [h19]
    nlinarith [h20, h21]
  have h19 : (k + 1) ^ 2 = a * b + 2 * k + 1 := by 
    nlinarith [h18]
  have h21 : (m + 1) * (n + 1) = ((2 * a + b + 3) * (a + 2 * b + 3)) / 9 := by
    rw [h14, h15]
    ring_nf
  rw [h19, h21]
  have h16 : 0 < b - a := by linarith
  nlinarith [sq_pos_of_pos ha, sq_nonneg (a - b), sq_nonneg (r - 1), sq_nonneg (d), 
            sq_nonneg (k - a - b / 2), sq_nonneg (k^2 - a * b), 
            mul_pos ha (show 0 < b - a by linarith), 
            sq_nonneg (a * b ^ 2 - a ^ 2 * b), 
            mul_pos ha (show 0 < a by linarith), 
            h18, mul_pos ha (show 0 < k by linarith), 
            mul_pos (show 0 < k by linarith) (show 0 < b by linarith [hb, ha] ) 
           ]
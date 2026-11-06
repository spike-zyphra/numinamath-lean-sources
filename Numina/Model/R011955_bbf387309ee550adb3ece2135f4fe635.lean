import Mathlib

theorem algebra_162771 {a b : ℕ → ℝ}
    (ha0 : a 0 = 1) (hb0 : b 0 = 2)
    (han : ∀ n, a (n + 1) = (1 + a n + a n * b n) / b n)
    (hbn : ∀ n, b (n + 1) = (1 + b n + a n * b n) / a n) :
    a 2020 < 5 := by
  have h10 : ∀ k : ℕ, a k > 0 ∧ b k > 0 := by 
    intro k 
    induction' k using Nat.strongRecOn with k ih
    cases k with 
    | zero =>
      constructor 
      · -- Show $a_0 > 0$
        linarith [ha0]
      · -- Show $b_0 > 0$
        linarith [hb0]
    | succ k =>
      have h4 := ih k (by linarith) 
      have hk1 : a k > 0 := h4.1 
      have hk2 : b k > 0 := h4.2 
      constructor 
      · -- Show $a_{k+1} > 0$ 
        have hk3 : a (k + 1) = (1 + a k + a k * b k) / b k := han k 
        rw [hk3] 
        apply div_pos 
        all_goals nlinarith [hk1, hk2] 
      · -- Show $b_{k+1} > 0$ 
        have hk4 : b (k + 1) = (1 + b k + a k * b k) / a k := hbn k 
        rw [hk4] 
        apply div_pos 
        all_goals nlinarith [hk1, hk2]

  have h9 : ∀ (n : ℕ), 1 / (a n + 1) - 1 / (b n + 1) = 1 / 6 := by 
    intro n 
    induction' n using Nat.strongRecOn with n ih 
    cases n with 
    | zero =>
      have ha1 : a 0 = 1 := ha0 
      have hb1 : b 0 = 2 := hb0 
      rw [ha1, hb1] 
      norm_num
    | succ n =>
      have h20 := ih n (by omega) 
      have ha1 : a (n + 1) = (1 + a n + a n * b n) / b n := han n 
      have hb1 : b (n + 1) = (1 + b n + a n * b n) / a n := hbn n 
      have ha2 : a n > 0 := by 
        have h4 : a n > 0 := (h10 n).1 
        linarith 
      have ha3 : b n > 0 := by 
        have h4 : b n > 0 := (h10 n).2 
        linarith
      rw [ha1, hb1] 
      have hk2 : a n > 0 := ha2 
      have hk3 : b n > 0 := ha3 
      field_simp at h20 ⊢ 
      <;> nlinarith [sq_nonneg (a n), sq_nonneg (b n), mul_pos (show 0 < a n by linarith) (show 0 < b n by linarith)]

  have h41 := h9 2020 
  have ha2020 : a 2020 > 0 := (h10 2020).1 
  have hb2020 : b 2020 > 0 := (h10 2020).2
  have h42 : 1 / (a 2020 + 1) - 1 / (b 2020 + 1) = 1 / 6 := by
    simpa using h41

  have h43 : a 2020 < 5 := by 
    have h44 : 1 / (a 2020 + 1) - 1 / (b 2020 + 1) = 1 / 6 := h42 
    have ha3 : a 2020 > 0 := ha2020 
    have hb3 : b 2020 > 0 := hb2020 
    have hb4 : 1 / (a 2020 + 1) - 1 / (b 2020 + 1) = (b 2020 - a 2020) / ((a 2020 + 1) * (b 2020 + 1)) := by 
      field_simp 
      <;> ring 
    rw [hb4] at h44 
    have hb5 : (b 2020 - a 2020) / ((a 2020 + 1) * (b 2020 + 1)) = 1 / 6 := h44 
    have hb8 : (a 2020 + 1) * (b 2020 + 1) > 0 := mul_pos (by positivity) (by positivity) 
    have hb9 : (b 2020 - a 2020) / ((a 2020 + 1) * (b 2020 + 1)) = 1 / 6 := hb5 
    apply (div_eq_iff (by positivity)).mp at hb9 
    nlinarith [sq_nonneg (a 2020 - 2), sq_nonneg (b 2020 - 1), sq_nonneg (a 2020 * (b 2020 - a 2020)), sq_nonneg ((b 2020) - a 2020), sq_nonneg ((b 2020) ^ 2 - 1)]
  exact h43
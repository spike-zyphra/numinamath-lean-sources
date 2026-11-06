import Mathlib

theorem algebra_11175 {a b : ℕ → ℤ} (ha1 : a 1 = 3)
    (han : ∀ n > 0, a (n + 1) = 2 * a n + 2 ^ (n + 1) - 1)
    (hb : ∀ n > 0, b n = (a n - 1) / 2 ^ n) :
    ∀ n > 0, b n = n := by
  intro n hn
  have h1 : ∀ n > 0, a n = n * 2 ^ n + 1 := by 
    intro n hn
    induction n with 
    | zero => 
      exfalso 
      linarith
    | succ n ih =>
      cases n with
      | zero => 
        rw [ha1]
        norm_num
      | succ n => 
        have h2 := ih (by linarith)
        have h3 := han (n + 1) (by linarith)
        simp [show n + 1 + 1 = n + 2 by omega] at h3
        simp [h2] at h3 ⊢
        ring_nf at h3 ⊢
        <;> omega
  have h2 := h1 n hn
  have h3 := hb n hn
  rw [h3]
  rw [h2]
  have h5 : ((n * 2 ^ n + 1 - 1) : ℤ) = (n * (2 ^ n : ℤ)) := by
    cases n with 
    | zero => 
      exfalso 
      all_goals omega 
    | succ n => 
      simp [pow_succ, mul_add] 
      all_goals 
        ring_nf
      all_goals 
        omega 
  rw [h5]
  have h4 : ((n * (2 ^ n) ) : ℤ) / (2 ^ n : ℤ) = (n : ℤ) := by 
    have h11 : ((2 ^ n : ℤ)) ≠ 0 := by
      have h12 : n > 0 := hn
      have h13 : (2 ^ n : ℤ) > (0 : ℤ) := by 
        have h14 : n ≥ 1 := by omega 
        have h15 : (2 ^ n : ℤ) ≥ (2 ^ 1 : ℤ) := by 
          apply pow_le_pow_right
          all_goals 
            norm_num 
            all_goals omega
        have h16 : (2 ^ 1 : ℤ) = (2 : ℤ) := by norm_num 
        have h17 : (2 ^ n : ℤ) ≥ (2 : ℤ) := by linarith [h15, h16]
        all_goals 
          omega 
        all_goals 
          tauto 
      have h14 : (2 ^ n : ℤ) > (0 : ℤ) := by linarith [h13]
      omega 
    have h5 : ((n * (2 ^ n) ) : ℤ) = ((2 ^ n : ℤ) * (n : ℤ)) := by 
      ring 
      <;> omega 
    rw [h5]
    field_simp at *
    <;> ring_nf <;> omega 
  rw [h4]
  all_goals try { tauto }
  all_goals try { omega }
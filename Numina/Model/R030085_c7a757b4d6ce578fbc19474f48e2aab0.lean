import Mathlib

theorem algebra_297857 {a b : ℕ → ℝ} {p q : ℝ} (hp : p > 0) (hq : q > 0)
    (hsum : p + q = 1) (ha1 : a 1 = p) (hb1 : b 1 = q)
    (han : ∀ n ≥ 2, a n = a (n - 1) * b n)
    (hbn : ∀ n ≥ 2, b n = b (n - 1) / (1 - (a (n - 1))^2)) :
    ∀ n ≥ 2, a n = p / (1 + (n - 1) * p) ∧
    b n = (1 + (n - 2) * p) / (1 + (n - 1) * p) := by
  intro n hn
  have h4 : ∀ n : ℕ, n ≥ 2 → a n = p / (1 + (n - 1) * p) ∧ b n = (1 + (n - 2) * p) / (1 + (n - 1) * p) := by
    intro n hn2
    have h1 : a 1 = p := ha1
    have h2 : b 1 = q := hb1
    have hq1 : q = 1 - p := by linarith 
    have hp1 : p > 0 := hp
    have h1' : p + q = 1 := hsum
    induction n with 
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero =>
        exfalso
        linarith
      | succ n =>
        cases n with 
        | zero =>
          -- n = 2, so proving for k=2
          have ha2 : a 2 = a 1 * b 2 := by 
            specialize han 2 (by linarith)
            simpa using han
          have hb2_eq : b 2 = b 1 / (1 - (a 1) ^ 2) := by 
            specialize hbn 2 (by linarith)
            simpa using hbn
          -- Substitute to get forms for a_2, b_2
          have ha1_val : a 1 = p := ha1
          have hb1_val : b 1 = q := hb1
          have hb2_val : b 2 = 1 / (1 + p) := by 
            rw [hb2_eq]
            rw [hb1_val, ha1_val]
            rw [hq1] -- Substitute q = 1-p
            field_simp [(show 1 - p ^ 2 ≠ 0 by nlinarith), (show 1 + p ≠ 0 by nlinarith)]
            <;> nlinarith 
          have ha2_val : a 2 = p / (1 + p) := by
            rw [ha2]
            rw [ha1_val]
            rw [hb2_val]
            <;> field_simp [(show 1 + p ≠ 0 by nlinarith), (show p ≠ 0 by linarith)]
            <;> ring_nf <;> field_simp [(show p ≠ 0 by linarith)]
            <;> nlinarith
          constructor
          · -- Prove a 2 = p / (1 + (2 - 1) * p)
            rw [ha2_val]
            field_simp
            <;> ring_nf <;> field_simp
            <;> nlinarith
          · -- Prove b 2 = (1 + (2 - 2) * p) / (1 + (2 - 1) * p)
            rw [hb2_val]
            field_simp
            <;> ring_nf <;> field_simp
            <;> nlinarith
        | succ n =>
          -- induction step, from k = n+2 (hypothesis) to k = n+3
          -- Here n is the induction variable for the hypothesis
          have h6 : n + 1 + 1 ≥ 2 := by linarith
          rcases ih (by linarith) with ⟨ha2, hb2⟩
          -- Goal index: k = n+3
          have ha3 : a (n + 1 + 1 + 1) = a (n + 1 + 1) * b (n + 1 + 1 + 1) := by 
            have h7 := han (n + 1 + 1 + 1) (by linarith)
            simpa using h7
          have hb3 : b (n + 1 + 1 + 1) = b (n + 1 + 1) / (1 - (a (n + 1 + 1)) ^ 2) := by 
            have h8 := hbn (n + 1 + 1 + 1) (by linarith)
            simpa using h8
          constructor
          · -- Prove the first part of the conjunction
            rw [ha3, hb3]
            rw [ha2, hb2]
            field_simp [(show 1 + ((↑n + 1 : ℝ) ) * p ≠ 0 by positivity), 
              (show 1 + ((↑n + 2 : ℝ) ) * p ≠ 0 by positivity)]
            ring_nf
            <;> field_simp [(show 1 + ((↑n + 1 : ℝ) ) * p ≠ 0 by positivity), 
              (show 1 + ((↑n + 2 : ℝ) ) * p ≠ 0 by positivity)]
            <;> ring 
          · -- Prove the second part of the conjunction
            rw [hb3]
            rw [ha2, hb2]
            field_simp [(show 1 + ((↑n + 1 : ℝ) ) * p ≠ 0 by positivity), 
              (show 1 + ((↑n + 2 : ℝ) ) * p ≠ 0 by positivity)]
            ring_nf
            <;> field_simp [(show 1 + ((↑n + 1 : ℝ) ) * p ≠ 0 by positivity), 
              (show 1 + ((↑n + 2 : ℝ) ) * p ≠ 0 by positivity)]
            <;> ring
  specialize h4 n hn
  simpa using h4
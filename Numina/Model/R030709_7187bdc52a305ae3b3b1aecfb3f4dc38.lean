import Mathlib



theorem number_theory_96875 :
  let PossibleNumber (n : ℕ) := (0 ≤ n) ∧ (∃ w: ℕ, 0 ≤ w ∧ w ≤ n ∧ (n+3) * (95: ℝ)/100 ≤ (1+w));
  PossibleNumber 37 ∧ ∀ n: ℕ, PossibleNumber n → 37 ≤ n := by
  apply And.intro
  .
    norm_num
    exists 37
    norm_num
  .
    intro n h
    let ⟨ hn, he ⟩ := h;
    cases he with
    | intro w hw =>
      let ⟨ hwpos, ⟨ hwn, hratio ⟩⟩ := hw
      by_contra h
      push_neg at h
      have h1 : (n : ℝ) < (37 : ℝ) := by
        exact_mod_cast h
      have h4 : (n + 3 : ℝ) * (95 : ℝ) ≤ (1 + (w : ℝ) ) * 100 := by
        linarith
      have h4' : (n + 3) * 95 ≤ (1 + w) * 100 := by
        have h4 : (n + 3 : ℝ) * 95 ≤ (1 + (w : ℝ) ) * 100 := h4
        exact_mod_cast h4
      have h5 : w ≤ n := by
        omega
      have h6 : n < 37 := by
        omega
      have h9 : n < 37 := by
        omega
      have h9_n : n ≤ 36 := by 
        omega
      have h8 : w ≤ 36 := by 
        nlinarith
      interval_cases n <;> try { omega } <;> try { 
        have h8 : w ≤ 36 := by 
          omega
        interval_cases w <;> norm_num at h4' ⊢
      }
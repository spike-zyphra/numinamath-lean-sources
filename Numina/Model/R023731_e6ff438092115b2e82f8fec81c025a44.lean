import Mathlib


theorem number_theory_307583 :
    {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 2 * (a + b + c)}.encard = 15 := by
  have h1 : {(a, b, c) : ℕ × ℕ × ℕ | a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 2 * (a + b + c)} = Finset.filter (fun s : ℕ × ℕ × ℕ => 
    (s.1 > 0 ∧ s.2.1 > 0 ∧ s.2.2 > 0 ∧ s.1 * s.2.1 * s.2.2 = 2 * (s.1 + s.2.1 + s.2.2))
    ) (Finset.Icc (0 : ℕ) 8 ×ˢ Finset.Icc (0 : ℕ) 8 ×ˢ Finset.Icc (0 : ℕ) 8) := by
    ext ⟨a, b, c⟩
    simp
    intro ha hb hc h_eq
    have h2 : a ≤ 8 := by
      by_contra h
      push_neg at h
      have h3 : b ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      have h4 : c ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      interval_cases b <;> interval_cases c
      <;> omega
    have h3 : b ≤ 8 := by
      by_contra h
      push_neg at h
      have h4 : a ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      have h5 : c ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      interval_cases a <;> interval_cases c
      <;> omega
    have h4 : c ≤ 8 := by
      by_contra h
      push_neg at h
      have h5 : a ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      have h6 : b ≤ 4 := by
        nlinarith [mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (b : ℕ) by linarith), 
          mul_pos (show 0 < (b : ℕ) by linarith) (show 0 < (c : ℕ) by linarith), 
          mul_pos (show 0 < (a : ℕ) by linarith) (show 0 < (c : ℕ) by linarith)]
      interval_cases a <;> interval_cases b
      <;> omega
    simp [Finset.mem_Icc, h2, h3, h4]
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide
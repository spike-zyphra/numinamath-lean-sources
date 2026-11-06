import Mathlib


theorem algebra_99471 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ 100 * (a + b) = a * b - 100}.encard = 18 := by

  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ 100 * (a + b) = a * b - 100} = Finset.filter (fun p : ℕ × ℕ => (p.1 > 0 ∧ p.2 > 0 ∧ 100 * (p.1 + p.2) = p.1 * p.2 - 100)) (Finset.Icc (0 : ℕ) 10200 ×ˢ Finset.Icc (0 : ℕ) 10200) := by
    ext ⟨a, b⟩
    simp
    intro ha hb heq
    have h2 : a ≤ 10200 := by
      by_contra h
      push_neg at h
      have heq1 : a * b = 100 * (a + b) + 100 := by
        omega
      have h3 : b ≤ 100 := by
        nlinarith [show 0 < a by linarith, show 0 < b by linarith]
      nlinarith [show 0 < a by linarith, show 0 < b by linarith]

    have heq2 : b ≤ 10200 := by
      by_contra h
      push_neg at h
      have heq1 : a * b = 100 * (a + b) + 100 := by
        omega
      have h4 : a ≤ 100 := by
        nlinarith [show 0 < a by linarith, show 0 < b by linarith]
      nlinarith [show 0 < a by linarith, show 0 < b by linarith]

    tauto

  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide
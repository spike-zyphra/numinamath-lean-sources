import Mathlib

theorem algebra_13915 :
    {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 10 ∧ |b| ≤ 10 ∧ |c| ≤ 10 ∧ |d| ≤ 10 ∧
      (c ^ 2 + a * c + b = 0 ∧ d ^ 2 + a * d + b = 0) ∧
      (a ^ 2 + c * a + d = 0 ∧ b ^ 2 + c * b + d = 0)}.ncard = 22 := by
  have h1 : {(a, b, c, d) : ℤ × ℤ × ℤ × ℤ | |a| ≤ 10 ∧ |b| ≤ 10 ∧ |c| ≤ 10 ∧ |d| ≤ 10 ∧
      (c ^ 2 + a * c + b = 0 ∧ d ^ 2 + a * d + b = 0) ∧
      (a ^ 2 + c * a + d = 0 ∧ b ^ 2 + c * b + d = 0)} = Finset.filter (fun s : ℤ × ℤ × ℤ × ℤ => 
        let (a, b, c, d) := s
        |a| ≤ 10 ∧ |b| ≤ 10 ∧ |c| ≤ 10 ∧ |d| ≤ 10 ∧
        (c ^ 2 + a * c + b = 0 ∧ d ^ 2 + a * d + b = 0) ∧
        (a ^ 2 + c * a + d = 0 ∧ b ^ 2 + c * b + d = 0)
      ) (Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10 : ℤ) 10 ×ˢ Finset.Icc (-10 : ℤ) 10) := by
    ext ⟨a, b, c, d⟩
    simp
    intro h1 h2 h3 h4 h5 h6 h7 h8
    have h9 : a ≤ 10 := by
      linarith [abs_le.mp h1]
    have h10 : a ≥ -10 := by
      linarith [abs_le.mp h1]
    have h11 : b ≤ 10 := by
      linarith [abs_le.mp h2]
    have h12 : b ≥ -10 := by
      linarith [abs_le.mp h2]
    have h13 : c ≤ 10 := by
      linarith [abs_le.mp h3]
    have h14 : c ≥ -10 := by
      linarith [abs_le.mp h3]
    have h15 : d ≤ 10 := by
      linarith [abs_le.mp h4]
    have h16 : d ≥ -10 := by
      linarith [abs_le.mp h4]
    tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide
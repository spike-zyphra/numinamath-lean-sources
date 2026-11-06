import Mathlib

theorem algebra_155271 :
    {(a1, a2, a3, a4, a5) : ℤ × ℤ × ℤ × ℤ × ℤ |
      1 = a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 = 15 ∧
      a2^2 ≤ a1 * a3 + 1 ∧ a3^2 ≤ a2 * a4 + 1 ∧ a4^2 ≤ a3 * a5 + 1}.ncard = 3 := by
  have h1 : {(a1, a2, a3, a4, a5) : ℤ × ℤ × ℤ × ℤ × ℤ |
      1 = a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 = 15 ∧
      a2^2 ≤ a1 * a3 + 1 ∧ a3^2 ≤ a2 * a4 + 1 ∧ a4^2 ≤ a3 * a5 + 1} = Finset.filter (fun s : ℤ × ℤ × ℤ × ℤ × ℤ => 
      1 = s.1 ∧ s.1 < s.2.1 ∧ s.2.1 < s.2.2.1 ∧ s.2.2.1 < s.2.2.2.1 ∧ s.2.2.2.1 < s.2.2.2.2 ∧ s.2.2.2.2 = 15 ∧
      s.2.1^2 ≤ s.1 * s.2.2.1 + 1 ∧ s.2.2.1^2 ≤ s.2.1 * s.2.2.2.1 + 1 ∧ s.2.2.2.1^2 ≤ s.2.2.1 * s.2.2.2.2 + 1
    ) (Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20 ×ˢ Finset.Icc (-10 : ℤ) 20) := by
    ext ⟨a1, a2, a3, a4, a5⟩
    simp
    all_goals omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide
import Mathlib

theorem algebra_163112 :
    Set.ncard {(a, b, c) : ℕ × ℕ × ℕ | 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100 ∧
      a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2} = 29800 := by
  have h : {(a, b, c) : ℕ × ℕ × ℕ | 1 ≤ a ∧ a ≤ 100 ∧ 1 ≤ b ∧ b ≤ 100 ∧ 1 ≤ c ∧ c ≤ 100 ∧
    a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2} = Finset.filter (fun x => 
        (1 ≤ x.1 ∧ x.1 ≤ 100) ∧ (1 ≤ x.2.1 ∧ x.2.1 ≤ 100) ∧ (1 ≤ x.2.2 ∧ x.2.2 ≤ 100) ∧ (x.1^2 * x.2.1 + x.2.1^2 * x.2.2 + x.2.2^2 * x.1 = x.1 * x.2.1^2 + x.2.1 * x.2.2^2 + x.2.2 * x.1^2))
        (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b, c⟩
    simp
    <;> omega
  rw [h]
  rw [Set.ncard_coe_Finset]
  native_decide
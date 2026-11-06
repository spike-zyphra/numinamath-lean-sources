import Mathlib

theorem algebra_22114 :
    Set.ncard {(a, b, c) : ℤ × ℤ × ℤ | 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ≤ 100 ∧ b ≤ 100 ∧ c ≤ 100 ∧ a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2} = 29800 := by
  have h1 : {(a, b, c) : ℤ × ℤ × ℤ | 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ≤ 100 ∧ b ≤ 100 ∧ c ≤ 100 ∧ a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2} = Finset.filter (fun s : ℤ × ℤ × ℤ => 
    let (a, b, c) := s
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a ≤ 100 ∧ b ≤ 100 ∧ c ≤ 100 ∧ a^2 * b + b^2 * c + c^2 * a = a * b^2 + b * c^2 + c * a^2
  ) (Finset.Icc (1 : ℤ) 100 ×ˢ Finset.Icc (1 : ℤ) 100 ×ˢ Finset.Icc (1 : ℤ) 100) := by
    ext ⟨a, b, c⟩
    simp
    <;> try { omega }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide
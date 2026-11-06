import Mathlib

theorem number_theory_88419 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ 100 ≤ a ∧ a ≤ 1000 ∧ 100 ≤ b ∧ b ≤ 1000 ∧
      Nat.gcd a b * 495 = Nat.lcm a b}.ncard = 20 := by
        have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ 100 ≤ a ∧ a ≤ 1000 ∧ 100 ≤ b ∧ b ≤ 1000 ∧
            Nat.gcd a b * 495 = Nat.lcm a b} = Finset.filter (fun s => 
              s.1 > 0 ∧ s.2 > 0 ∧ s.1 < s.2 ∧ 100 ≤ s.1 ∧ s.1 ≤ 1000 ∧ 100 ≤ s.2 ∧ s.2 ≤ 1000 ∧
              Nat.gcd s.1 s.2 * 495 = Nat.lcm s.1 s.2) (Finset.Icc (0 : ℕ) 1000 ×ˢ Finset.Icc (0 : ℕ) 1000) := by
            ext ⟨a, b⟩
            simp
            omega
        rw [h1]
        rw [Set.ncard_coe_Finset]
        native_decide
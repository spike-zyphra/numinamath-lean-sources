import Mathlib

theorem number_theory_610694: ∑ᶠ x ∈ {x: ℕ | 10 ≤ x ∧ x < 100 ∧
  ∀ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ x ∣ 100 * a + 10 * b + c →
    x ∣ 100 * b + 10 * c + a}, x = 64 := by
  have h1 : {x: ℕ | 10 ≤ x ∧ x < 100 ∧
    ∀ a b c, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ x ∣ 100 * a + 10 * b + c →
      x ∣ 100 * b + 10 * c + a} = 
      Finset.filter (fun x : ℕ => 10 ≤ x ∧ x < 100 ∧ 
        ∀ (a : ℕ), 1 ≤ a → a ≤ 9 → ∀ (b : ℕ), b ≤ 9 → ∀ (c : ℕ), c ≤ 9 → 
          x ∣ 100 * a + 10 * b + c → x ∣ 100 * b + 10 * c + a) (Finset.Icc 0 99) := by
    ext n
    simp
    <;> aesop <;> omega
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide
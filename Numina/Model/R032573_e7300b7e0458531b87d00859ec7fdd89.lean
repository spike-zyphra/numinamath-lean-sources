import Mathlib

theorem number_theory_128388 : {a : ℕ | a ∣ (2^4 * 3^2 * 5)}.encard = 30 := by
  have h1 : {a : ℕ | a ∣ (2^4 * 3^2 * 5)} = Finset.filter (λ x => x ∣ (2^4 * 3^2 * 5)) (Finset.Icc 0 (2^4 * 3^2 * 5 : ℕ)) := by
    ext n
    simp
    intro h
    have : n ≤ 2^4 * 3^2 * 5 := by
      exact Nat.le_of_dvd (show 0 < 2^4 * 3^2 * 5 by norm_num) h 
    omega 
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide
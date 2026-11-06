import Mathlib

theorem number_theory_91233 {n : ℕ} (hn : n = Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ 2007}) :
    Odd n ∧ ¬(3 ∣ n) := by 
  have h1 : n = Set.ncard {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ 2007} := hn
  have h2 : {p : ℤ × ℤ | p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ 2007} = Finset.filter (fun p : ℤ × ℤ => p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2 ≤ 2007) (Finset.Icc (-100 : ℤ) 100 ×ˢ Finset.Icc (-100 : ℤ) 100) := by
    ext ⟨x, y⟩
    simp
    intro h
    have h4 : x ^ 2 + x * y + y ^ 2 ≤ 2007 := by
      nlinarith
    have h5 : x ≤ 100 := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (y - 2 * x), sq_nonneg (2 * y + x), sq_nonneg (x - y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y + 100), sq_nonneg (x + y - 100)]
    have h6 : x ≥ -100 := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (y - 2 * x), sq_nonneg (2 * y + x), sq_nonneg (x - y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y + 100), sq_nonneg (x + y - 100)]
    have h7 : y ≤ 100 := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (2 * y - x), sq_nonneg (x + 2 * y), sq_nonneg (x - y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y + 100), sq_nonneg (x + y - 100)]
    have h8 : y ≥ -100 := by
      nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (2 * y - x), sq_nonneg (x + 2 * y), sq_nonneg (x - y), sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y + 100), sq_nonneg (x + y - 100)]
    all_goals tauto
  rw [h1] at *
  rw [h2]
  rw [Set.ncard_coe_Finset]
  constructor
  · -- Show that n is odd
    native_decide
  · -- Show that n is not divisible by 3
    native_decide
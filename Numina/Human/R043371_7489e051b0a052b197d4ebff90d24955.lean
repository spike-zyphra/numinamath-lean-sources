import Mathlib

theorem number_theory_4904 {n : ℕ} :
    ∏ x ∈ Nat.divisors n, x = (n ^ (Nat.divisors n).card).sqrt := by
  let ds := Nat.divisors n
  have h₀ : ∀ x ∈ ds, n / x * x = n := fun x hx => Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hx)
  have h₁ : ∏ d ∈ ds, n / d = ∏ d ∈ ds, d := Nat.prod_div_divisors n id
  convert (Nat.sqrt_eq (∏ x ∈ ds, x)).symm using 2
  nth_rw 1 [← h₁]
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl h₀, Finset.prod_const]

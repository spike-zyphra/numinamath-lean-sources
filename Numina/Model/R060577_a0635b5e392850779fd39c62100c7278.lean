import Mathlib

def sumOfDigits (n : ℕ) := (Nat.digits 10 n).sum

theorem number_theory_162527 (a : ℕ → ℕ)
    (h₀ : a 0 = 934)
    (h₁ : ∀ n, a (n + 1) = 13 * sumOfDigits (a n)) :
    a 2018 = 130 := by
  have ha1 : a 1 = 208 := by
    rw [h₁ 0, h₀]
    norm_num [sumOfDigits]
  have ha2 : a 2 = 130 := by
    rw [h₁ 1, ha1]
    norm_num [sumOfDigits]
  have ha3 : a 3 = 52 := by
    rw [h₁ 2, ha2]
    norm_num [sumOfDigits]
  have ha4 : a 4 = 91 := by
    rw [h₁ 3, ha3]
    norm_num [sumOfDigits]
  have ha5 : a 5 = 130 := by
    rw [h₁ 4, ha4]
    norm_num [sumOfDigits]

  have h2 : ∀ k, a (2 + 3 * k) = 130 := by
    intro k
    induction k with
    | zero =>
      have h : a 2 = 130 := ha2
      simpa using h
    | succ k ih =>
      have h21 : a (2 + 3 * k) = 130 := ih
      have h11 : a ( (2 + 3 * k) + 1 ) = 52 := by
        rw [h₁ ( (2 + 3 * k) )]
        rw [h21]
        norm_num [sumOfDigits]
      have h12 : a ( (2 + 3 * k) + 2 ) = 91 := by
        rw [h₁ ( (2 + 3 * k) + 1 )]
        rw [h11]
        norm_num [sumOfDigits]
      have h13 : a ( (2 + 3 * k) + 3 ) = 130 := by
        rw [h₁ ( (2 + 3 * k) + 2 )]
        rw [h12]
        norm_num [sumOfDigits]
      have h3 : (2 + 3 * (k + 1)) = (2 + 3 * k) + 3 := by
        ring_nf
      rw [h3]
      exact h13
  have h3 : 2018 = 2 + 3 * 672 := by
    omega
  rw [h3] at *
  apply h2 672
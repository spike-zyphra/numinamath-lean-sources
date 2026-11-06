import Mathlib

/- Inserting one of the digits from $0$, $1$, $2$, $\cdots $, $9$ between the hundreds and tens place of a three-digit number results in a four-digit number that is exactly $9$ times the original three-digit number. The smallest such three-digit number is ___          ___ , and the largest is ___          ___. -/
theorem number_theory_2791 (n : ℕ) (h₀ : n ∈ Finset.Icc 100 999) (h₁ : (100 * n + 10 * k + l) = 9 * n) :
    n = 125 ∨ n = 675 := by 
  rw [Finset.mem_Icc] at h₀
  rcases h₀ with ⟨h3, h4⟩
  omega
import Mathlib

theorem algebra_225181 {P : Polynomial ℤ} (a b : ℤ) (h₀ : a > b) :
    (P.eval a - P.eval b) % (a - b) = 0 := by
  have h1 : (a - b) ∣ (P.eval a - P.eval b) := by
    apply Polynomial.sub_dvd_eval_sub
  exact Int.emod_eq_zero_of_dvd h1
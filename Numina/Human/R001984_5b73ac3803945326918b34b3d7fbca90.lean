import Mathlib

/- PROBLEM: For any positive integer k, let f(k) denote the square of the sum of the digits of k. 
For n≥2, let f^n(k)=f(f^(n−1)(k)). Find f1988(11). -/
def f (k : ℕ) : ℕ := (Nat.digits 10 k).sum ^ 2

theorem number_theory_52307 : f^[1988] 11 = 169 := by {
  have f11: ∀ n ≥ 4, (Even n → f^[n] 11 = 169) ∧ (Odd n → f^[n] 11 = 256) := by {
    apply Nat.le_induction
    constructor
    intro h4
    unfold f
    norm_num
    trivial
    intros n hnge hn
    constructor
    rw [Nat.even_add_one, Nat.not_even_iff_odd]
    intro hodd
    cases hn with
     | intro hl hr => {
       rw [Function.iterate_succ', Function.comp, hr hodd]
       unfold f
       norm_num
      }
    cases hn with
     | intro hl hr => {
         rw [Nat.odd_add_one, Nat.not_odd_iff_even]
         intro heven
         rw [Function.iterate_succ', Function.comp, hl heven]
         unfold f
         norm_num
     }
  }
  
  have := f11 1988 (by trivial)
  cases this with
    | intro hl hr => {
      apply hl
      trivial
  }
}
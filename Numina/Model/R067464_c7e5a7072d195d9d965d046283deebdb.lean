import Mathlib

theorem algebra_1038 (father son: ℕ) (son_age : father = Nat.ofDigits 10 [son % 10, son / 10]) (h : father = 3 * son + 6) :
    father - son = 36 := by
  simp [Nat.ofDigits, List.foldl] at son_age h ⊢
  omega
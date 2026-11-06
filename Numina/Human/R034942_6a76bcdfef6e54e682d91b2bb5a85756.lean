import Mathlib

/- Let n=8^2022. Which of the following is equal to 
n/4?
(A) 4^1010   (B) 2^2022   (C) 8^2018   (D) 4^3031   (E) 4^3032
  -/
theorem algebra_93488 {n : ℕ} (hn : n = 8 ^ 2022) : n / 4 = 4 ^ 3032 := by
--substitute n in the expression
    rw[hn]
--compute numerically the expression
    have h1: 8^2022 = 2^(3*2022) := by norm_num
    have h2: 4 = 2^2 := by rfl
    rw[h1,h2, Nat.pow_div, ← Nat.pow_mul 2 2 3032,]
    · linarith
    · linarith
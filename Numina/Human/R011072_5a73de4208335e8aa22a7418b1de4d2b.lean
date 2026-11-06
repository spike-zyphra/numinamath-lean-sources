import Mathlib

open Real

/- Let a sequence $b_1, b_2, \ldots$ be defined as $b_1 = 1$, $b_2 = 2$, and $b_{n+1} = b_n b_{n-1}$.  Calculate $b_{20}$ -/
theorem algebra_10985
    (b : ℕ → ℕ)
    (hb0 : b 0 = 1)
    (hb1 : b 1 = 2)
    (hbn : ∀ n, b (n + 2) = b (n) * b (n + 1)) :
    b 19 = 2 ^ 4181 := by

  -- aux prop, b * > 0
  have r_bpos : ∀ n, b n > 0 := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    cases n
    case zero => simp [hb0]
    case succ n =>
      cases n
      case zero => simp [hb1]
      case succ n =>
        simp [hbn]
        constructor <;>
        exact ih _ (by omega)

  -- Notice that every term $b_n$ will be a power of 2, the exponent of which will be the sum of the exponents of the two previous terms.  Therefore, let us construct a sequence $a_1, a_2, \ldots$, such that $a_1 = 0$, and $a_2 = 1$, and $a_{n+1} = a_n + a_{n-1}$.
  let a : ℕ → ℝ := fun n => logb 2 (b n)
  have ha0 : a 0 = 0 := by simp [a, hb0]
  have ha1 : a 1 = 1 := by simp [a, hb1]
  have han : ∀ n, a (n + 2) = a (n) + a (n + 1) := by
    intro n
    specialize hbn n
    apply_fun (logb 2) at hbn
    dsimp [a]
    convert hbn using 1
    rw [Nat.cast_mul, logb_mul]
    all_goals simp [Nat.not_eq_zero_of_lt (r_bpos _)]


  -- Therefore, let us construct a sequence $a_1, a_2, \ldots$, such that $a_1 = 0$, and $a_2 = 1$, and $a_{n+1} = a_n + a_{n-1}$.  Of course, $a_{20}$ is simply equivalent to the 19th term of the Fibonacci Sequence, 4181.
  have rva19 : a 19 = 4181 := by
    simp only [han, ha1, ha0]
    norm_num

  -- Thus, $b_{20} = 2^{a_{20}} = \boxed{2^{4181}}$.
  have rvb19 : b 19 = (2 : ℝ) ^ (a 19) := by
    simp [a]
    refine Eq.symm (rpow_logb ?b_pos ?b_ne_one ?hx)
    . linarith only
    . linarith only
    . exact Nat.cast_pos'.mpr (r_bpos 19)

  rify
  rw [rvb19, rva19]
  norm_num

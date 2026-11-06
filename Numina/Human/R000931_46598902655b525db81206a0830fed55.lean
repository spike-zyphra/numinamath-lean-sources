import Mathlib

/- The UPC code, made up of numbers and dashes, on a video tape is 9-78094-11006-$x$. The digit $x$ is in the $12^{\mathrm{th}}$ position. Let $n$ be the value obtained by adding the digits in the odd positions, tripling that sum, and then adding the digits in the even positions. A valid UPC code is such that $n$ is divisible by 10. For what value of $x$ will this UPC code be valid? -/
theorem number_theory_19181 (x : ℕ) (hx : x < 10)
    (hsum : 10 ∣ (3 * (∑ i in Finset.range 6, (Nat.digits 10 97809411006 ++ [x])[2 * i]!) + ∑ i in Finset.range 6, (Nat.digits 10 97809411006 ++ [x])[2 * i + 1]!)) : x = 9 := by
    -- simplify the expression
    simp [Nat.digits, Finset.range, List.range, Nat.digitsAux] at hsum
    ring_nf at hsum
    -- replace the division hypothesis with a multiplication hypothesis
    have h1 : ∃ k : ℕ, 111 + x = k * 10 := dvd_iff_exists_eq_mul_left.mp hsum
    -- intro k
    rcases h1 with ⟨k, hk⟩
    -- have k = 12
    have hk1 : k = 12 := by linarith
    -- solve the equation
    linarith

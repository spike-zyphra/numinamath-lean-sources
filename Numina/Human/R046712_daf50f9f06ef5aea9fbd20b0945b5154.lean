import Mathlib

open GCDMonoid (gcd)

/- If \( a_{1}, a_{2}, \ldots, a_{n} \) are integers that are not all zero, then the greatest common divisor of the integers \( (a_{1}, a_{2}, \ldots, a_{n-1}, a_{n}) \) is equal to the greatest common divisor of the integers \( (a_{1}, a_{2}, \ldots, (a_{n-1}, a_{n})) \).-/
theorem number_theory_4505 {a : ℕ → ℤ} (n : ℕ) (d : ℤ) : (∀ i ∈ Finset.range (n+2), d ∣ a i) ↔
    (∀ i ∈ Finset.range n, d ∣ a i) ∧ d ∣ Int.gcd (a n) (a (n+1)) := by
  constructor
  intro h
  constructor
  -- Let \( d \) be any common divisor of the \( n \) integers \( a_{1}, a_{2}, \ldots, a_{n-1}, a_{n} \). By definition, this means that \( d \) divides each of these integers. In particular, \( d \) must divide both \( a_{n-1} \) and \( a_{n} \). Therefore, \( d \) is also a divisor of the greatest common divisor of \( a_{n-1} \) and \( a_{n} \), denoted as \( (a_{n-1}, a_{n}) \).
  . intro i hi
    simp at hi
    have hi' : i ∈ Finset.range (n+2) := Finset.mem_range.mpr (by linarith)
    exact h i hi'
  . rw [show (a n).gcd _ = gcd (a n) _ from rfl, dvd_gcd_iff]
    have hn : n ∈ Finset.range (n+2) := Finset.mem_range.mpr (by linarith)
    have hnsucc : (n+1) ∈ Finset.range (n+2) := Finset.mem_range.mpr (by linarith)
    exact ⟨h _ hn, h _ hnsucc⟩
--    Now, consider any common divisor \( e \) of the \( n-2 \) integers \( a_{1}, a_{2}, \ldots, a_{n-2} \) and the greatest common divisor \( (a_{n-1}, a_{n}) \). Since \( e \) divides \( (a_{n-1}, a_{n}) \), it must also divide both \( a_{n-1} \) and \( a_{n} \). Consequently, \( e \) is a common divisor of all \( n \) integers \( a_{1}, a_{2}, \ldots, a_{n-1}, a_{n} \).
-- Since any common divisor of the \( n \) integers is also a common divisor of the first \( n-2 \) integers and \( (a_{n-1}, a_{n}) \), and vice versa, we conclude that the sets of common divisors for both groups are identical. Therefore, the greatest common divisors of the two sets must be equal, leading us to the conclusion that:
-- \[
-- (a_{1}, a_{2}, \ldots, a_{n-1}, a_{n}) = (a_{1}, a_{2}, \ldots, (a_{n-1}, a_{n})).
-- \]
  intro h i hi
  rcases lt_or_ge i n with hin | hin
  . have hi' : i ∈ Finset.range n := Finset.mem_range.mpr (by linarith)
    exact h.1 _ hi'
  simp at hi
  have hi_n_or_nsucc : i = n ∨ i = n+1 := by omega
  rcases hi_n_or_nsucc with hin | hinsucc
  . rw [hin]
    trans ((a n).gcd (a (n+1)) : ℤ)
    . exact h.2
    . exact Int.gcd_dvd_left
  . rw [hinsucc]
    trans ((a n).gcd (a (n+1)) : ℤ)
    . exact h.2
    . exact Int.gcd_dvd_right

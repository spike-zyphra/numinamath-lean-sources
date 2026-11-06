import Mathlib

/-
Let $m$ be a positive integer such that $m$ is greater than 2 and the value of Euler's totient function $\phi(m)$ is 2. Show that the set of prime numbers $p$ such that $p \equiv m-1 \pmod m$ is infinite.
-/

theorem number_theory_641369 (m: ℕ) (mge2: 2 ≤ m) (hm: m.totient = 2):
  {p : ℕ | Nat.Prime p ∧ ((p: ZMod m) = m-1)}.Infinite := by
  
  --We apply the Dirichlet's Theorem.
  let a : ZMod m := (m-1)
  have ha : IsUnit a := by 
    unfold IsUnit
    use (-1)
    simp [a]
  apply Nat.setOf_prime_and_eq_mod_infinite at ha
  simp [a] at ha
  
  have : @HSub.hSub (ZMod m) (ZMod m) (ZMod m) instHSub (↑m) 1 = -1 := by 
    simp

  rw [this]
  exact ha

  exact NeZero.of_gt mge2
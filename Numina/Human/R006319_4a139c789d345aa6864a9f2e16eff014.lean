import Mathlib

open Nat

/- Lemma: An inductive sequence defined by $u_0 = 0$, $u_1 = 1$, and $u_k = u_{k-1} + u_{k-2}$ for all $k \ge 2$ is equal to the Fibonacci sequence. -/
lemma lemma_1 {u : ℕ → ℕ} (hu₀ : u 0 = 0) (hu₁ : u 1 = 1) (huk : ∀ k ≥ 2, u k = u (k - 1) + u (k - 2)) : u = fib := by
  -- We show that u_n = fib n for all n.
  ext n
  -- We use two step induction on n.
  induction n using twoStepInduction with
  | zero => simp [hu₀] -- u_0 = 0 = fib 0
  | one => simp [hu₁] -- u_1 = 1 = fib 1
  | more n ih₁ ih₂ => simpa [huk, fib_add_two, ih₁, ih₂] using add_comm _ _ -- u_n = u_{n-1} + u_{n-2} = fib n-1 + fib n-2 = fib n

/- Let $u$ be a sequence of natural numbers defined by $u_0 = 0$, $u_1 = 1$, and $u_k = u_{k-1} + u_{k-2}$ for all $k \ge 2$. Let $d$ be a positive integer such that $d$ divides $u_d$. Prove that for any natural number $n$, if $d$ divides $n$, then $d$ divides $u_n$. -/
theorem number_theory_635849 (u : ℕ → ℕ) (hu₀ : u 0 = 0) (hu₁ : u 1 = 1) (huk : ∀ k ≥ 2, u k = u (k - 1) + u (k - 2)) (d : ℕ) (hd : 0 < d) (hud : d ∣ u d) (n : ℕ) (hn : d ∣ n) : d ∣ u n := by
  have Hu := lemma_1 hu₀ hu₁ huk
  subst u
  -- If m ∣ n, then fib m ∣ fib n
  -- So d ∣ fib d ∣ fib n
  calc d
    _ ∣ fib d := hud
    _ ∣ fib n := fib_dvd _ _ hn
import Mathlib

open Finset

/- Lemma: The number of integers $k$ in the interval $[1, n]$ such that $\operatorname{gcd}(n, k) = d$ is equal to $\phi(n/d)$. -/
lemma lemma_1 {n d : ℕ} (hnd : d ∣ n) :
    (n / d).totient = #{k ∈ Icc 1 n | n.gcd k = d}:= by
  -- We use the library lemma that the number of integers $k$ in the interval $[0, n)$ such that $\operatorname{gcd}(n, k) = d$ is equal to $\phi(n/d)$.
  convert Nat.totient_div_of_dvd hnd using 1
  -- We show that there is a bijection between the set of integers $k$ in the interval $[1, n]$ such that $\operatorname{gcd}(n, k) = d$ and the set of integers $k$ in the interval $[0, n)$ such that $\operatorname{gcd}(n, k) = d$.
  -- We define a function that maps $n$ to $0$ and all other integers $k$ in the interval $[0, n)$ to $k$.
  apply Finset.card_bij (i := fun a ha => if a = n then 0 else a)
  . -- We first show that the function maps into the set in the target.
    intro a ha
    simp at ha ⊢
    -- We distinguish between the case where $a = n$ and the case where $a \neq n$.
    split_ifs with h
    . subst a
      simpa using ha
    . exact ⟨lt_of_le_of_ne ha.1.2 h, ha.2⟩
  . -- We show that the function is injective.
    intro a₁ ha₁ a₂ ha₂ heq
    simp at ha₁ ha₂ ⊢
    -- We distinguish between the case where $a_1 = n$ and the case where $a_1 \neq n$.
    -- Also, we distinguish between the case where $a_2 = n$ and the case where $a_2 \neq n$.
    split_ifs at heq with h₁ h₂ h₂
    . exact h₁.trans h₂.symm
    . simp [← heq] at ha₂
    . simp [heq] at ha₁
    . exact heq
  . -- We show that the function is surjective.
    intro b hb
    simp at hb ⊢
    -- The inverse function is given by $f^{-1}(0) = n$ and $f^{-1}(k) = k$ for $k \neq 0$.
    use if b = 0 then n else b
    -- We distinguish between the case where $b = 0$ and the case where $b \neq 0$.
    -- Also, we distinguish between the case where $a = n$ and the case where $a \neq n$.
    split_ifs with h₁ h₂ h₂
    . subst h₁
      simpa using hb
    . simp at h₂
    . simp [h₂] at hb
    . exact ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr h₁, hb.1.le⟩, hb.2⟩, rfl⟩

/- Let $N$ be a positive integer. For positive integers $m, k$, let $\operatorname{gcd}(m, k)$ denote the largest positive integer that is a factor of both $m$ and $k$. Compute the sum
$$ \sum_{n=1}^{N} \operatorname{gcd}(n, N). $$
Show that the sum is equal to $\sum_{d|N} d \cdot \phi(N/d)$, where $\phi$ is Euler's totient function and the sum is over all positive divisors $d$ of $N$. -/
theorem number_theory_635718 (N : ℕ) (hN₀ : 0 < N) :
    ∑ n ∈ Icc 1 N, n.gcd N = ∑ d ∈ N.divisors, d * (N / d).totient := by
  -- We change the order of gcd.
  conv_lhs =>
    arg 2
    ext n
    rw [Nat.gcd_comm]
  -- We use the library lemma that the sum of a function over a set is equal to the sum of the function over the fibers of the function.
  -- We show that any possible value of the gcd is a divisor of N.
  have H := Finset.sum_fiberwise_of_maps_to' (f := id) (s := Icc 1 N) (g := N.gcd) (t := N.divisors) (by intro i _; simpa [hN₀.ne'] using Nat.gcd_dvd_left _ _)
  simp at H
  rw [← H]
  -- Now we show the summands are equal.
  refine Finset.sum_congr rfl fun x hx => ?_
  -- We just use the lemma proved above.
  rw [lemma_1 (Nat.dvd_of_mem_divisors hx), mul_comm]
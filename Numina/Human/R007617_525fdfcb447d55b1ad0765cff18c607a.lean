import Mathlib

/- Show that there exist infinitely many positive integers $n$ such that

$$
\frac{4^{n}+2^{n}+1}{n^{2}+n+1}
$$

is an integer. -/
theorem number_theory_605133 :
    { n | n > 0 ∧ n ^ 2 + n + 1 ∣ 4 ^ n + 2 ^ n + 1 }.Infinite := by
  -- Let f(n) = n^2 + n + 1
  let f n := n ^ 2 + n + 1
  -- We have f(n) divides f(n^2)
  have H₁ n : f n ∣ f (n ^ 2) := by
    -- Expand and cast to ℤ
    ring_nf
    zify
    -- Factorize 1 + n^2 + n^4
    rw [show (1 + n ^ 2 + n ^ 4 : ℤ) = (1 + n + n ^ 2) * (1 - n + n ^ 2) by ring]
    simp
  -- By induction, f(n) divides f(n^(2^k))
  have H₂ n k : f n ∣ f (n ^ 2 ^ k) := by
    induction k with
    | zero => simp [f]
    | succ k ih =>
      rw [pow_succ, pow_mul]
      exact ih.trans (H₁ _)
  -- The condition in the problem is equivalent to f(n) ∣ f(2^n)
  -- So as long as there are infinitely many n such that 2^n = n^(2^k), we're done
  suffices H : { n | n > 0 ∧ ∃ k, 2 ^ n = n ^ 2 ^ k }.Infinite by
    apply H.mono
    rintro n ⟨h₁, k, h₂⟩
    simp [h₁]
    rw [show 4 ^ n = (2 ^ n) ^ 2 by rw [show 4 = 2 ^ 2 by simp]; exact Nat.pow_right_comm 2 2 n]
    change f n ∣ f (2 ^ n)
    rw [h₂]
    exact H₂ _ _
  -- We can construct a strictly increasing function g(m) = 2^(2^m)
  -- Such that any g(m) is a solution to the problem
  -- So there are infinitely many solutions
  let g m := 2 ^ 2 ^ m
  have hg : StrictMono g := by
    intro m n h
    exact Nat.pow_lt_pow_of_lt (by simp) (Nat.pow_lt_pow_of_lt (by simp) h)
  apply StrictMono.injective at hg
  apply Set.infinite_of_injective_forall_mem (f := g) hg
  -- We now show that every g(m) is a solution to the problem
  intro m
  simp [g]
  -- where k = 2 ^ m - m
  use 2 ^ m - m
  rw [← pow_mul]
  congr 1
  -- Show m ≤ 2 ^ m
  have hm : m ≤ 2 ^ m := le_of_lt Nat.lt_two_pow_self
  nth_rw 1 [show 2 ^ m = m + (2 ^ m - m) from (Nat.add_sub_of_le hm).symm]
  exact Nat.pow_add _ _ _

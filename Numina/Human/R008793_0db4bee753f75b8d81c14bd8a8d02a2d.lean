import Mathlib

/-Vind alle functies $f: \mathbb{Z} \rightarrow \mathbb{Z}$ die voldoen aan

$$
f(m+n)+f(m n-1)=f(m) f(n)+2
$$

voor alle $m, n \in \mathbb{Z}$.-/
theorem algebra_606284 (f : ℤ → ℤ) : (∀ m n, f (m + n) + f (m * n - 1) = f m * f n + 2) ↔
∀ n, f n = n ^ 2 + 1 := by
  constructor
  -- Prove that $f$ is not constant
  · intro heq; have f_ne_const : ¬ ∃ c, ∀ n, f n = c := by
      rintro ⟨c, hc⟩; simp [hc] at heq; have := two_mul_le_add_pow_two c 1; linarith
  -- Plug in $m=0$, $n=0$ and $m=0$, $n=n'$ such that $f(n')≠f(0)$ to heq and find $f(0)=1$
    push_neg at f_ne_const; have f0 : f 0 = 1 := by
      obtain ⟨n', hn'⟩ := f_ne_const (f 0)
      have aux1 := heq 0 0; have aux2 := heq 0 n'; simp at aux1 aux2
      apply_fun fun t => t - (f 0 + f (-1)) at aux2; nth_rw 2 [aux1] at aux2
      ring_nf at aux2; rw [pow_two, ← sub_mul, ] at aux2; symm at aux2
      rw [mul_right_eq_self₀] at aux2; rcases aux2 with _|h; assumption
      rw [sub_eq_zero] at h; contradiction
  -- Plug in $m=0$, $n=0$ to heq to find $f(-1)=2$
    have fm1 : f (-1) = 2 := by specialize heq 0 0; simp [f0] at heq; linarith
  -- Plug in $m=-1$, $n=-1$ to heq to find $f(-2)=5$
    have fm2 : f (-2) = 5 := by specialize heq (-1) (-1); simp [fm1, f0] at heq; linarith
  -- Plug in $m=1$, $n=-1$ to heq to find $f(1)=2$
    have f1 : f 1 = 2 := by specialize heq 1 (-1); simp [f0, fm2, fm1] at heq; linarith
  -- Specialize heq at $m=1$ and simplify it, we get a recursive relation on the values of $f$
    specialize heq 1; simp [f1] at heq; intro n; induction n with
  -- Use two step induction to prove that $f(n)=n^2+1$
    | ofNat n =>
      induction n using Nat.twoStepInduction; simp [f0]; simp [f1]
      rename_i n ih1 ih2; specialize heq (n+1); simp at *; ring_nf at *
      symm at heq; rw [← sub_eq_iff_eq_add] at heq; rw [← heq, ih2, ih1]; ring
    | negSucc n =>
      induction n using Nat.twoStepInduction; simp [fm1]; simp [fm2]
      rename_i n ih1 ih2; rw [Int.negSucc_eq] at *; push_cast at *; specialize heq (-n-2)
      ring_nf at *; symm at heq; rw [← sub_eq_iff_eq_add'] at heq
      rw [← heq, ih2, ih1]; ring
-- Conversely, it is straightforward to check that $f(n)=n^2+1$ satisfies the functional equation in question
  intro h m n; simp [h]; ring
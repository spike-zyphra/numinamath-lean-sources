import Mathlib

/- Let $c_r$ be an integer. Let the sequence $a_n$ for $n \in \mathbb{N}$ (non-negative integers) be defined by $a_0=1$, and for $n \ge 0$, $a_{n+1} = a_n+1$ if $n$ is even, and $a_{n+1}=c_r$ if $n$ is odd.
Let $k$ be a non-negative integer. Determine the value of $a_k$.
Show that $a_k=1$ if $k=0$; $a_k=2$ if $k=1$; $a_k=c_r$ if $k \ge 2$ and $k$ is even; and $a_k=c_r+1$ if $k \ge 2$ and $k$ is odd. -/
theorem number_theory_639463 (cr : ℕ) (a : ℕ → ℤ) (k : ℕ) (h₀ : a 0 = 1)
    (h₁ : ∀ n, Even n → a (n + 1) = a n + 1) (h₂ : ∀ n, Odd n → a (n + 1) = cr) :
    if k = 0 then a k = 1 else if k = 1 then a k = 2 else if Even k then a k = cr else a k = cr + 1 :=
by
  rcases em (k = 0) with (kh0|kh0)
  . subst kh0
    simp
    assumption
  rcases em (k = 1) with (kh1|kh1)
  . subst kh1
    simp
    rw [h₁ 0]
    rw [h₀]
    rfl
    decide
  simp [kh0, kh1]
  rcases em (Even k) with (khe|khe)
  . simp [khe]
    let k' := k - 1
    have : Odd k' := by
      refine Nat.Even.sub_odd ?_ khe ?_
      omega
      decide
    rw [show k = k' + 1 by simp [k']; zify; rw [Nat.cast_sub]; omega; omega]
    apply h₂
    assumption
  . simp [khe]
    simp at khe
    let k' := k - 1
    have : Even k' := by
      simp [k']
      refine Odd.tsub_odd khe ?_
      decide
    rw [show k = k' + 1 by simp [k']; zify; rw [Nat.cast_sub]; omega; omega]
    rw [h₁]
    let k'' := k' - 1
    have : Odd k'' := by
      apply Nat.Even.sub_odd
      simp [k']
      zify
      rw [Nat.cast_sub]
      omega
      omega
      assumption
      decide
    rw [show k' = k'' + 1 by simp [k'']; zify; rw [Nat.cast_sub]; omega; omega]
    rw [h₂]
    assumption
    assumption

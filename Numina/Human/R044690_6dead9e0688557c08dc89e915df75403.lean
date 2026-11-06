import Mathlib

/-Determine all functions $f$ defined in the set of rational numbers and taking their values in the same set such that the equation $f(x+y)+f(x-y)=2 f(x)+2 f(y)$ holds for all rational numbers $x$ and $y$.-/
theorem algebra_26705 : {f : ℚ → ℚ | ∀ x y : ℚ, f (x + y) + f (x - y) = 2 * f x + 2 * f y} =
    {f : ℚ → ℚ | ∃ a : ℚ, ∀ x, f x = a * x^2} := by
  ext f
  simp
  constructor
  . intro h
    -- Insert $x=y=0$ in the equation to obtain $2 f(0)=4 f(0)$, which implies $f(0)=0$. 
    have h1 : f 0 = 0 := by 
      specialize h 0 0
      simp at h
      linarith
    -- Setting $x=0$, one obtains $f(y)+f(-y)=2 f(y)$ of $f(-y)=f(y)$.
    have h2 : ∀ y, f y = f (-y) := by
      intro y
      specialize h 0 y
      simp [h1] at h
      linarith
    -- Then assume $y=n x$, where $n$ is a positive integer. We obtain
    -- $$
    -- f((n+1) x)=2 f(x)+2 f(n x)-f((n-1) x)
    -- $$
    have h3 (n : ℕ) : ∀ x, f ((n + 1) * x) = 2 * f x + 2 * f (n * x) -f ((n - 1) * x) := by
      intro x
      specialize h x (n * x)
      ring_nf at h ⊢
      rw [show x - x * n = - (-x + x * n) by linarith, ←h2 (-x + x * n)] at h
      linarith
    -- We prove $f(n x)=n^{2} f(x)$ for all positive integers $n$. This is true for $n=1$. Assume $f(k x)=k^{2} f(x)$ for $k \leq n$. Then

    -- $$
    -- \begin{aligned}
    -- & f((n+1) x)=2 f(x)+2 f(n x)-f((n-1) x) \\
    -- & =\left(2+2 n^{2}-(n-1)^{2}\right) f(x)=(n+1)^{2} f(x)
    -- \end{aligned}
    -- $$
    -- and we are done. 
    have h4 (n : ℕ) : ∀ x, f (n * x) = n^2 * f x := by
      intro x
      induction' n using Nat.twoStepInduction with n ind1 ind2
      · simp [h1]
      · simp [h1]
      · simp [h1]
        simp at ind1 ind2
        have := h3 (n + 1) x
        push_cast at this ind2
        rw [show (n : ℚ) + 1 + 1 = (n : ℚ) + 2 by linarith] at this
        rw [this, ind2, show (n : ℚ) + 1 - 1 = n by linarith, ind1]
        linarith
    -- If $x=1 / q$, where $q$ is a positive integer, $f(1)=f(q x)=q^{2} f(x)$. So $f(1 / q)=f(1) / q^{2}$. 
    have h5 (x : ℚ) (hx : x.num = 1) : f x = f 1 / x.den^2 := by 
      specialize h4 x.den x 
      simp [hx] at h4
      field_simp
      linarith
    
    use f 1
    intro x
    wlog xpos : 0 ≤ x
    · have := this f h h1 h2 h3 h4 h5
      have negx : 0 ≤ -x := by linarith
      rw [h2 x, show x^2 = (-x)^2 by norm_num]
      exact this (-x) negx
    -- trivial lemma about rational number.
    have h6 : x = x.num * (1 / x.den) := by nth_rw 1 [←Rat.num_div_den x, mul_one_div]
    rw [←Rat.num_nonneg] at xpos
    have h7 := h4 (x.num.toNat) (1 / x.den)
    have h6' : x = x.num.toNat * (1 / x.den) := by
      nth_rw 1 [h6]
      simp
      norm_cast
      rw [Int.toNat_of_nonneg xpos]
    rw [←h6'] at h7
    specialize h5 (1 / x.den) (by simp; exact Int.sign_ofNat_of_nonzero (by simp))
    nth_rw 2 [one_div] at h5
    simp only [ Rat.inv_natCast_den, Rat.den_ne_zero, ↓reduceIte] at h5
    rw [h5] at h7
    -- So $f(1 / q)=f(1) / q^{2}$. This again implies $f(p / q)=p^{2} f(1 / q)=(p / q)^{2} f(1)$. We have shown that there is a rational number $a=f(1)$ such that $f(x)=a x^{2}$ for all positive rational numbers $x$.
    have : f x = f 1 * (x.num.toNat / x.den)^2 := by field_simp at h7 ⊢; linarith
    rw [mul_one_div] at h6'
    rw [←h6'] at this
    exact this
  · --  In fact, if $f(x)=a x^{2}$, then $f(x+y)+f(x-y)=a(x+y)^{2}+a(x-y)^{2}=2 a x^{2}+2 a y^{2}=2 f(x)+2 f(y)$. So the required functions are all functions $f(x)=a x^{2}$ where $a$ is any rational number.
    intro ⟨a, ha⟩ x y
    rw [ha (x + y), ha (x - y), ha x, ha y]
    linarith

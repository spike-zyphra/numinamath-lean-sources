import Mathlib

/-Suppose that there exist nonzero complex numbers $a, b, c$, and $d$ such that $k$ is a root of both the equations $a x^{3}+b x^{2}+c x+d=0$ and $b x^{3}+c x^{2}+d x+a=0$.
  Find all possible values of $k$ (including complex values).-/
theorem algebra_608626 : {k :ℂ | ∃ a b c d : ℂ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0 ∧
  a * k^3 + b * k^2 + c * k + d = 0 ∧ b * k^3 + c * k^2 + d * k + a = 0} = {1, -1, -Complex.I, Complex.I} := by
  -- $1,-1, i,-i$
  apply Set.ext ;intro k ;simp ;constructor
  intro h
  rcases h with ⟨a, ha, b, hb, c, hc, d, hd, hk1, hk2⟩
  -- Let $k$ be a root of both polynomials.
  -- Multiplying the first polynomial by $k$ and subtracting the second, we have $a k^{4}-a=0$,
  have h1 : k * (a * k ^ 3 + b * k ^ 2 + c * k + d) - (b * k ^ 3 + c * k ^ 2 + d * k + a) =
    a * k ^ 4 - a := by ring
  simp [hk1, hk2] at h1 ;nth_rewrite 2 [← mul_one a] at h1 ;rw [← mul_sub] at h1 ;simp [ha] at h1
  -- which means that $k$ is either $1,-1, i$, or $-i$.
  have h2 : (k ^ 2) ^ 2 = 1 := by
    rw [← pow_mul] ;norm_num ;rw [← zero_add 1] ;exact sub_eq_iff_eq_add.mp h1
  simp at h2
  rcases h2 with (h2 | h2) | h2
  simp [h2] ;simp [h2]
  right ;right
  have : (k - Complex.I) * (k + Complex.I) = 0 := by
    rw [sub_mul,mul_add,mul_add,← pow_two,h2] ;simp ;ring_nf
  simp at this
  rcases this with (this | this)
  right ;rw [← zero_add Complex.I] ;exact sub_eq_iff_eq_add.mp this
  left ;exact eq_neg_of_add_eq_zero_left this
  intro hk
  -- If $a=b=c=1$ and $d=-3$, then 1 is a root of both polynomials.
  rcases hk with hk | hk
  use 1,(by simp),1,(by simp),1,(by simp),-3,(by simp)
  simp [hk] ;ring_nf ;simp
  -- If $a=b=c=d=1$, then $-1, i$, and $-i$ are roots of both polynomials.
  use 1,(by simp),1,(by simp),1,(by simp),1,(by simp)
  simp [hk,pow_two,pow_three]
  rcases hk with hk | (hk | hk)
  · simp [hk]
  · simp [hk]
  · simp [hk]
  -- So $k$ can be $1,-1, i$, and $-i$.
  
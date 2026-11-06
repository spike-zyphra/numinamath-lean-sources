import Mathlib

/-Let $\omega$ be a complex number such that
\[\omega + \frac{1}{\omega} = 1.\]Find all possible values of
\[\omega^n + \frac{1}{\omega^n},\]where $n$ is a positive integer.

Enter all possible values, separated by commas.-/
theorem algebra_22062 {ω : ℂ} (hω : ω ≠ 0) (h : ω + 1 / ω = 1) :
  {m | ∃ n, 0 < n ∧ m = ω^n + 1 / ω^n } = {-2, -1, 1, 2} := by
    -- From the equation $\omega + \frac{1}{\omega} = 1,$ $\omega^2 + 1 = \omega,$ so
    -- \[\omega^2 - \omega + 1 = 0.\]Then $(\omega + 1)(\omega^2 - \omega + 1) = 0,$ which expands as $\omega^3 + 1 = 0.$  Hence, $\omega^3 = -1.$
    have h1 : ω^3 = -1 := by 
      field_simp at h 
      have : ω^2 - ω + 1 = 0 := by nth_rw 2 [← h]; norm_num [pow_two]
      have : (ω + 1) * (ω^2 - ω + 1) = 0 := by norm_num [this]
      have : ω^3 + 1 = 0 := by ring_nf at this; ring_nf; assumption
      exact Eq.symm (neg_eq_of_add_eq_zero_left this)
    -- auxiliary equation :  $\omega^2 + \frac{1}{(\omega^2) = -1$.
    have h' : ω^2 + (ω^2)⁻¹ = -1 := by 
      apply_fun (· ^ 2) at h 
      ring_nf at h 
      have : ω * ω⁻¹ = 1 := by field_simp
      norm_num [this] at h 
      linear_combination h  
    ext m
    simp 
    constructor 
    · intro ⟨n, _, hk⟩ 
      have : ∃ k, n = 3 * k ∨ n = 3 * k + 1 ∨ n = 3 * k + 2 := by 
        rw [← Nat.div_add_mod n 3]
        mod_cases n % 3  <;> 
        use n / 3 <;> simp <;> tauto  
      obtain ⟨k, hk1⟩ := this 
      -- If $n = 3k,$ then
      -- \[\omega^n + \frac{1}{\omega^n} = \omega^{3k} + \frac{1}{\omega^{3k}} = (\omega^3)^k + \frac{1}{(\omega^3)^k} = (-1)^k + \frac{1}{(-1)^k}.\]If $k$ is even, then this becomes 2, and if $k$ is odd, then this becomes $-2.$

      -- If $n = 3k + 1,$ then
      -- \begin{align*}
      -- \omega^n + \frac{1}{\omega^n} &= \omega^{3k + 1} + \frac{1}{\omega^{3k + 1}} = (\omega^3)^k \omega + \frac{1}{(\omega^3)^k \omega} \\
      -- &= (-1)^k \omega + \frac{1}{(-1)^k \omega} \\
      -- &= (-1)^k \frac{\omega^2 + 1}{\omega} \\
      -- &= (-1)^k \frac{-\omega}{\omega} \\
      -- &= (-1)^k.
      -- \end{align*}This can be $1$ or $-1$.

      -- And if $n = 3k + 2,$ then
      -- \begin{align*}
      -- \omega^n + \frac{1}{\omega^n} &= \omega^{3k + 2} + \frac{1}{\omega^{3k + 2}} = (\omega^3)^k \omega^2 + \frac{1}{(\omega^3)^k \omega^2} \\
      -- &= (-1)^k \omega^2 + \frac{1}{(-1)^k \omega^2} \\
      -- &= (-1)^k \frac{\omega^4 + 1}{\omega^2} \\
      -- &= (-1)^k \frac{-\omega + 1}{\omega^2} \\
      -- &= (-1)^k \frac{-\omega^2}{\omega^2} \\
      -- &= -(-1)^k.
      -- \end{align*}This can be $1$ or $-1$.

      -- Hence, the possible values of $\omega^n + \frac{1}{\omega^n}$ are $\boxed{-2,-1,1,2}.$
      rcases hk1 with hk1 | hk1 | hk1 
      <;> norm_num [hk1, pow_mul, pow_add, h1] at hk
      <;> rcases Nat.even_or_odd k with eok | eok 
      <;> try simp [eok] at hk; norm_num at h; norm_num [hk, h, h', ← neg_add]
    · intro hk
      rcases hk with  hk | hk | hk | hk 
      · use 3; norm_num [hk, h1]
      · use 2; norm_num [hk, h']
      · use 1; ring_nf at h; norm_num [hk, h]
      · use 6
        simp
        rw [show 6 = 3 + 3 by ring_nf, pow_add, h1]
        norm_num [hk]



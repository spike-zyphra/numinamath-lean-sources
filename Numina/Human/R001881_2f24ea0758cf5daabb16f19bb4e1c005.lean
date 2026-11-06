import Mathlib

/- Find the smallest positive integer $n$ for which we can find an integer $m$ such that $\left[\frac{10^n}{m}\right] = 1989$. -/
theorem number_theory_42078 :
    IsLeast {n : ℕ | ∃ m : ℕ, ⌊(10 ^ n / m : ℝ)⌋ = 1989} 7 := by
    constructor
    -- For ( n = 7 ): [ \frac{10^7}{1990} &lt; m \leq \frac{10^7}{1989} ] [ \frac{10000000}{1990} &lt; m \leq \frac{10000000}{1989} ] [ 5025.1256 &lt; m \leq 5027.1386 ] Here, ( m ) can be 5026 or 5027.
    -- Verify:
    -- For ( m = 5026 ): [ \left\lfloor \frac{10^7}{5026} \right\rfloor = \left\lfloor 1989.004 \right\rfloor = 1989 ]
    · simp ;use 5026 ;norm_num
    apply mem_lowerBounds.mpr 
    intro x hx
    simp at hx
    rcases hx with ⟨m,hm⟩
    -- We need to find the smallest positive integer ( n ) such that there exists an integer ( m ) for which (\left\lfloor \frac{10^n}{m} \right\rfloor = 1989).
    have hm' : 0 < m := by
      refine Nat.zero_lt_of_ne_zero ?_
      by_contra!
      simp [this] at hm
    apply Int.floor_eq_iff.mp at hm
    rcases hm with ⟨hm1, hm2⟩
    -- This implies the inequality: [ 1989 \leq \frac{10^n}{m} &lt; 1990 ] which can be rewritten as: [ \frac{10^n}{1990} &lt; m \leq \frac{10^n}{1989} ]
    apply (le_div_comm₀ (by simp) (by simp [hm'])).mp at hm1
    apply (div_lt_iff₀ (by simp [hm'])).mp at hm2
    rw [mul_comm] at hm2
    apply (div_lt_iff₀ (by simp ;norm_num)).mpr at hm2
    -- We will check for the smallest ( n ) starting from ( n = 1 ) and increasing until we find a suitable ( m ).
    by_cases hx : x < 7
    · interval_cases x
      <;> norm_num at hm1 hm2
      · have : m < 1 ∧ m > 0 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 1 ): [ \frac{10^1}{1990} &lt; m \leq \frac{10^1}{1989} ] [ \frac{10}{1990} &lt; m \leq \frac{10}{1989} ] [ 0.005 &lt; m \leq 0.00503 ] No integer ( m ) satisfies this inequality.
      · have : m < 1 ∧ m > 0 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 2 ): [ \frac{10^2}{1990} &lt; m \leq \frac{10^2}{1989} ] [ \frac{100}{1990} &lt; m \leq \frac{100}{1989} ] [ 0.05025 &lt; m \leq 0.05028 ] No integer ( m ) satisfies this inequality.
      · have : m < 1 ∧ m > 0 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 3 ): [ \frac{10^3}{1990} &lt; m \leq \frac{10^3}{1989} ] [ \frac{1000}{1990} &lt; m \leq \frac{1000}{1989} ] [ 0.5025 &lt; m \leq 0.5028 ] No integer ( m ) satisfies this inequality.
      · have : m < 1 ∧ m > 0 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 4 ): [ \frac{10^4}{1990} &lt; m \leq \frac{10^4}{1989} ] [ \frac{10000}{1990} &lt; m \leq \frac{10000}{1989} ] [ 5.025 &lt; m \leq 5.028 ] No integer ( m ) satisfies this inequality.
      · have : m < 6 ∧ m > 5 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 5 ): [ \frac{10^5}{1990} &lt; m \leq \frac{10^5}{1989} ] [ \frac{100000}{1990} &lt; m \leq \frac{100000}{1989} ] [ 50.25 &lt; m \leq 50.28 ] No integer ( m ) satisfies this inequality.
      · have : m < 51 ∧ m > 50 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
      -- For ( n = 6 ): [ \frac{10^6}{1990} &lt; m \leq \frac{10^6}{1989} ] [ \frac{1000000}{1990} &lt; m \leq \frac{1000000}{1989} ] [ 502.51 &lt; m \leq 502.76 ] No integer ( m ) satisfies this inequality.
      · have : m < 503 ∧ m > 502 := by
          constructor
          rify ;linarith
          rify ;linarith
        linarith
    -- Thus, the smallest ( n ) for which there exists an integer ( m ) such that (\left\lfloor \frac{10^n}{m} \right\rfloor = 1989) is ( n = 7 ).
    -- The final answer is ( \boxed{ n = 7 } )
    push_neg at hx ;exact hx




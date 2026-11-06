import Mathlib
open Finset
open Real
open BigOperators

/- 
Let $N$ be a positive natural number. Let $\lfloor x \rfloor$ denote the greatest integer function, which gives the greatest integer less than or equal to $x$.
Show that $\sum\limits_{k=0}^{N}{\left\lfloor \frac{N+{{2}^{k}}}{{{2}^{k+1}}} \right\rfloor} = N$.
-/
theorem number_theory_640534(N: ℕ)(h: 0 < N): ∑ k ∈ range (N+1), ⌊(N + 2^k : ℝ)/(2^(k+1))⌋ = N := by 
  -- Let $S_N$ be the sum we want to evaluate:\
  -- $$S_N = \\sum\\limits\_{k=0}^{N}{\\left\\lfloor \\frac{N+{{2}^{k}}}{{{2}^{k+1}}} \\right\\rfloor}$$\
  -- Let $a_k$ be the term in the sum:\
  -- $$a_k = \\left\\lfloor \\frac{N+{{2}^{k}}}{{{2}^{k+1}}} \\right\\rfloor$$\
  -- We can rewrite the expression inside the floor function:\
  -- $$\\frac{N+{{2}^{k}}}{{{2}^{k+1}}} = \\frac{N}{{{2}^{k+1}}} + \\frac{2^k}{2^{k+1}} = \\frac{N}{{{2}^{k+1}}} + \\frac{1}{2}$$
  have h₀(k: ℕ): (N + 2^k : ℝ)/(2^(k+1)) = (N:ℝ)/(2^(k+1)) + (1:ℝ)/2 := by field_simp; ring

  -- We use the identity for the floor function: $\\lfloor x + 1/2 \\rfloor = \\lfloor 2x \\rfloor - \\lfloor x \\rfloor$. 
  -- This identity holds for any real number $x$.
  -- We can prove it as follows:
  have h₁ (x): ⌊x + (1:ℝ)/2⌋ =  ⌊2*x⌋ - ⌊x⌋ := by 
    -- Let $x = I + f$, where $I = \\lfloor x \\rfloor$ is an integer and $0 \\le f &lt; 1$ is the fractional part of $x$.
    let I := ⌊x⌋
    let f := Int.fract x
    have h₀: x = I + f := by exact Eq.symm (Int.floor_add_fract x)
    
    -- The left side (LHS) is $\\lfloor I + f + 1/2 \\rfloor$.
    rw[h₀]

    have h₁: 0 ≤ f ∧ f < (1:ℝ)/2 ∨ (1:ℝ)/2 ≤ f ∧ f < 1 := by 
      simp_rw[f, Int.fract_nonneg, Int.fract_lt_one, true_and, and_true]
      exact lt_or_ge (Int.fract x) (1 / 2)
    
    -- The right side (RHS) is $\\lfloor 2(I+f) \\rfloor - \\lfloor I+f \\rfloor = \\lfloor 2I+2f \\rfloor - I$.
    have h₂ :  ⌊2 * (↑I + f)⌋ - ⌊↑I + f⌋ =  ⌊2 * ↑I + 2 * f⌋ - I := by ring_nf; congr; exact h₀.symm

    rcases h₁ with h | h
    · -- case: 0 ≤ f ∧ f < 1 / 2
      -- If $0 \\le f &lt; 1/2$, then $1/2 \\le f+1/2 &lt; 1$. So LHS = $I$.
      have lhs: ⌊I + f + (1:ℝ) / 2⌋ = I := by 
        rw [Int.floor_eq_iff.mpr]
        constructor
        · linarith
        · linarith

      -- If $0 \\le f &lt; 1/2$, then $0 \\le 2f &lt; 1$. So $\\lfloor 2I+2f \\rfloor = 2I$. RHS = $2I-I = I$.
      have rhs:  ⌊2 * (↑I + f)⌋ - ⌊↑I + f⌋ = I := by 
        rw[h₂, sub_eq_iff_eq_add', Int.floor_eq_iff, ←(Int.two_mul I)]
        constructor
        · norm_cast
          linarith
        · simp
          linarith
      rw[lhs, rhs]

    · --  case:  1 / 2 ≤ f ∧ f < 1
      -- If $1/2 \\le f &lt; 1$, then $1 \\le f+1/2 &lt; 3/2$. 
      -- So LHS = $I+1$.
      have lhs: ⌊I + f + (1:ℝ) / 2⌋ = I + 1 := by 
        rw [Int.floor_eq_iff]
        constructor
        · norm_num
          linarith
        · norm_num
          linarith

      -- If $1/2 \\le f &lt; 1$, then $1 \\le 2f &lt; 2$. 
      -- So $\\lfloor 2I+2f \\rfloor = 2I+1$. RHS = $(2I+1)-I = I+1$.
      have rhs:  ⌊2 * (↑I + f)⌋ - ⌊↑I + f⌋ = I + 1 := by 
        rw[h₂, sub_eq_iff_eq_add', Int.floor_eq_iff, ←Int.add_assoc, ←(Int.two_mul I)]
        constructor
        · simp
          linarith
        · simp
          linarith
      rw[lhs, rhs]

  -- $$\\left\\lfloor 2 \\cdot \\frac{N}{2^{k+1}} \\right\\rfloor = \\left\\lfloor \\frac{N}{2^k} \\right\\rfloor$$
  have h₂ (x): 2 * ((N:ℝ) / 2 ^ (x + 1)) = ((N:ℝ) / 2^x ) := by ring_nf
  
  --   Now, we can rewrite the sum $S_N$:\
  -- $$S_N = \\sum\_{k=0}^{N} \\left( \\left\\lfloor \\frac{N}{2^k} \\right\\rfloor - \\left\\lfloor \\frac{N}{2^{k+1}} \\right\\rfloor \\right)$$\
  -- This is a telescoping sum. 
  -- Let $b_k = \\left\\lfloor \\frac{N}{2^k} \\right\\rfloor$. Then each term in the sum is $b_k - b\_{k+1}$.\
  -- $$S_N = (b_0 - b_1) + (b_1 - b_2) + (b_2 - b_3) + \\dots + (b_N - b\_{N+1})$$\
  -- The intermediate terms cancel out, leaving:\
  -- $$S_N = b_0 - b\_{N+1}$$
  have h₃ : ∑ x ∈ range (N + 1), (⌊(N:ℝ) / 2 ^ x⌋ - ⌊(N:ℝ) / 2 ^ (x + 1)⌋) = ⌊(N:ℝ) / 2 ^ 0⌋ - ⌊(N:ℝ) / 2 ^ (N+1)⌋ := by 
    apply Finset.sum_range_induction 
      (f := fun x => ⌊(N:ℝ) / 2 ^ x⌋ - ⌊(N:ℝ) / 2 ^ (x + 1)⌋)
      (s := fun x => ⌊(N:ℝ) / 2 ^ 0⌋ - ⌊(N:ℝ) / 2 ^ x⌋)
    · ring_nf
    · intro n
      ring

  -- $b_0 = \\left\\lfloor \\frac{N}{2^0} \\right\\rfloor = \\left\\lfloor \\frac{N}{1} \\right\\rfloor = \\lfloor N \\rfloor$. Since $N$ is a positive natural number, $\\lfloor N \\rfloor = N$.
  have h₄: (N:ℝ)  / 2 ^ 0 = N := by field_simp
  
  
  -- $b\_{N+1} = \\left\\lfloor \\frac{N}{2^{N+1}} \\right\\rfloor$.\
  -- We need to show that $b\_{N+1}=0$.
  have h₅: ⌊(N:ℝ) / 2 ^ (N + 1)⌋ = 0 := by 
    -- This requires showing that $0 \\le \\frac{N}{2^{N+1}} &lt; 1$.
    rw [Int.floor_eq_zero_iff, Set.mem_Ico]
    
    constructorm* _ ∧ _
    · -- Since $N$ is a positive natural number, $N \\ge 1$.\
      -- Therefore, $\\frac{N}{2^{N+1}} \\ge \\frac{1}{2^{N+1}} &gt; 0$.
      calc 0 <= (1:ℝ) / 2^(N+1) := by simp
        _ <= (N:ℝ) / 2^(N+1)    := by gcongr; exact Nat.one_le_cast.mpr h
    · -- Next, we need to show that $\\frac{N}{2^{N+1}} &lt; 1$,
      -- which is equivalent to $N &lt; 2^{N+1}$.
      refine Bound.div_lt_one_of_pos_of_lt (by positivity) ?_

      -- We can prove $N &lt; 2^N$ for all $N \\ge 1$ by induction:
      calc (N:ℝ) < 2 ^ N := by 
            clear h₀ h₁ h₂ h₃ h₄
            norm_cast
            induction' N, h using Nat.le_induction with m hi₁ hi₂
            · -- Base case: For $N=1$, $1 &lt; 2^1 = 2$. This is true.
              norm_num
            · -- Inductive hypothesis: Assume $m &lt; 2^m$ for some integer $m \\ge 1$.
              -- Inductive step: We want to show $m+1 &lt; 2^{m+1}$.

              -- By the inductive hypothesis, $2^m &gt; m$, so $2 \\cdot 2^m &gt; 2m$.
              rw [← (Nat.mul_lt_mul_left (by positivity: 0 < 2))] at hi₂

              -- We need to show that $2m \\ge m+1$. 
              suffices h: m + 1 ≤ 2 * m by
                --  This inequality is true if $m \\ge 1$.
                exact Nat.lt_two_pow_self
              -- So, for $m \\ge 1$, we have $m+1 \\le 2m &lt; 2 \\cdot 2^m = 2^{m+1}$.\
              -- Thus, $m+1 &lt; 2^{m+1}$.
              exact add_one_le_two_mul hi₁

          -- Since $2^N \\le 2^{N+1}$ for $N \\ge 0$ (in fact $2^N &lt; 2^{N+1}$ for $N \\ge 0$), we have $N &lt; 2^N \\le 2^{N+1}$.\
          -- So, $N &lt; 2^{N+1}$ for all $N \\ge 1$.
          _ < 2 ^ (N + 1) := by gcongr; norm_num; exact lt_add_one N

  -- Substituting the values of $b_0$ and $b\_{N+1}$ back into the expression for $S_N$:\
  -- $$S_N = N - 0 = N$$\
  -- Thus, we have shown that $\\sum\\limits\_{k=0}^{N}{\\left\\lfloor \\frac{N+{{2}^{k}}}{{{2}^{k+1}}} \\right\\rfloor} = N$.
  simp_rw[h₀, h₁, h₂, h₃, h₄, h₅, sub_zero, Int.floor_natCast]
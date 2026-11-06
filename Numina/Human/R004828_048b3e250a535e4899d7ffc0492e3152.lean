import Mathlib

/- 6. 126 Find all functions $f: Z^{*} \rightarrow R$ that satisfy
$f(n+m)+f(n-m) \equiv f(3 n), n, m \in Z^{*}\left(Z^{*}\right.$ 
is the set of non-negative integers), $n \geqslant m$. -/
theorem algebra_600793' (f : ℕ → ℝ) :
    (∀ n m, n ≥ m → f (n + m) + f (n - m) = f (3 * n)) ↔ ∀ n, f n = 0 := by 
  constructor
  -- First direction: if the function satisfies the equation, then it is zero
  · intro h n 
    have h0 : f 0 = 0 := by
      have := h 0 0 (by norm_num)
      simpa 
    induction n using Nat.strong_induction_on with
    | h n ih => 
      cases n with
      | zero =>
        exact h0
      | succ n =>
        by_cases hn : n ≥ 1 
        · -- case n ≥ 1
          have h1 := h n 1 hn 
          have h2 := h n 0 (by norm_num) 
          rw [← h2] at h1 
          simp only [add_zero, tsub_zero] at h1  
          have h3 := ih (n - 1) (by omega)
          have h4 := ih n (by norm_num)
          -- Apply inductive hypothesis,
          -- $$ f(n+1)+f(n-1)=f(n+1)=f(3n) \quad 0 = f (3n).$$
          rw [h3, h4] at h1 
          simpa using h1 
          -- So $f(n+1)=0$, done.
        · -- Case n = 0
          simp only [ge_iff_le, not_le, Nat.lt_one_iff] at hn 
          -- take $(n, m) = (1,0), (1, 1), (2, 0), (2, 2), (4, 0), (4, 2)$.
          have h10 := h 1 0 (by norm_num)
          have h11 := h 1 1 (by norm_num)
          have h20 := h 2 0 (by norm_num)
          have h22 := h 2 2 (by norm_num)
          have h40 := h 4 0 (by norm_num)
          have h42 := h 4 2 (by norm_num)
          simp at h10 h11 h20 h22 h40 h42
          have h3_eq : f 3 = 0 := by
            have eq6 : f 6 = 2 * f 3 := by
              linarith [h20, h11]
            have eq_f1 : f 1 = f 3 := by
              linarith [h11, h20, eq6]
            linarith
          -- Combine these equations to obtain $f(1)=0$.
          have h1_eq : f 1 = 0 := by
            linarith [h3_eq]
          simp [hn, h1_eq]  
  · -- Second direction: if f is zero, then it satisfies the equation
    intro h n m _ 
    simp [h]
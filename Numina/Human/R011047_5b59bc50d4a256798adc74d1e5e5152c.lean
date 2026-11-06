import Mathlib

/-
Let $a_{0}, a_{1}, a_{2}, \ldots$ be a sequence of real numbers defined by $a_{0}=21, a_{1}=35$, and $a_{n+2}=4 a_{n+1}-4 a_{n}+n^{2}$ for $n \geq 2$. Compute the remainder obtained when $a_{2006}$ is divided by 100 .
-/

theorem Algebra_611498  (a : ℕ → ℤ) (ha₀ : a 0 = 21) (ha₁ : a 1 = 35) (h: ∀ n : ℕ, 2≤ n → a (n) = 4 * a (n-1) - 4 * a (n-2) + n^2) :
  a 2006 % 100 = 36 := by

    -- get the expression for a n
    have han : ∀ n : ℕ, a n = (2*n+1) * 2^n + n^2 + 8*n + 20 := by 
      have tmp : ∀ x : ℕ, ∀ n : ℕ, n ≤ x → a n = (2*n+1) * 2^n + n^2 + 8*n + 20 := by
        intro x
        induction' x with x hx
        intro n hn
        have neq0 : n = 0 := by linarith
        rw [neq0]; simp; ring_nf; linarith
        intro n hn
        by_cases nx : n ≤ x
        apply hx; assumption
        have neqxp1 : n = x+1 := by linarith
        by_cases xeq0 : x = 0
        rw [xeq0] at neqxp1; norm_num at neqxp1; simp [neqxp1]; assumption
        have : 2≤ n := by rw [neqxp1]; omega
        have ind : a n = 4 * a (n - 1) - 4 * a (n - 2) + ↑n ^ 2 := h n this
        rw [hx (n - 1), hx (n - 2)] at ind
        rw [ind]; rify; field_simp; ring_nf
        have : (2:ℝ) ^ ( n- 1) * 8 = 2 ^ (n) *4  := by
          have : n = n - 1 + 1 := by omega
          nth_rw 2 [this];  rw [pow_succ]; ring_nf
        rw [mul_assoc]; rw [this]; 
        have t3: (2:ℝ) ^ ( n- 1) * 4 = 2 ^ (n) * 2  := by
          have : n = n - 1 + 1 := by omega
          nth_rw 2 [this];  rw [pow_succ]; ring_nf
        rw [t3];
        have : 8 = 4 * 2 := by norm_num
        have t4: (2:ℝ) ^ ( n- 2) * 8 = 2 ^ (n-1) * 4  := by
          have : n-1 = n-2+1 := by omega
          rw [this];  rw [pow_succ]; ring_nf
        rw [mul_assoc]; rw [t4]; rw [t3]; 
        have t5 : (2:ℝ) ^ ( n- 2) * 12 = 2 ^ (n-1) * 6  := by
          have : n-1 = n-2+1 := by omega
          rw [this];  rw [pow_succ]; ring_nf
        rw [t5];
        have t6 : (2:ℝ) ^ ( n- 1) * 6 = 2 ^ (n) * 3 := by
          have : n = n - 1 + 1 := by omega
          nth_rw 2 [this];  rw [pow_succ]; ring_nf
        rw [t6]; ring_nf
        omega
        omega
      intro n
      apply tmp n n; linarith
    
    have a2006 : a 2006 = (2 * 2006+1) * 2^2006 + 2006^2 + 8*2006 + 20 := by rw[han]; ring_nf

    -- Calculation in ZMod
    have l1: (2 * 2006 + 1) ≡ 13 [ZMOD 100] := by norm_num [Int.ModEq]
    have : 2^2006 % 100 = 64 := by ring_nf
    have l2: 2^2006 ≡ 64 [ZMOD 100] := by exact Int.modEq_iff_dvd.mpr (by norm_num [this])
    have l3: (2 * 2006+1) * 2^2006 ≡ 13 * 64 [ZMOD 100] := by exact Int.ModEq.mul l1 l2
    have l4: (2006^2 + 8*2006 +20) ≡ 4 [ZMOD 100] := by norm_num [Int.ModEq]
    have l5: (2 * 2006+1) * 2^2006 + (2006^2 + 8*2006 + 20) ≡ 13 * 64 + 4 [ZMOD 100] := by exact Int.ModEq.add l3 l4
    have l6: ((13 * 64)) + 4 ≡ 36 [ZMOD 100] := by norm_num [Int.ModEq]
    have l7: ((2:ℤ) * 2006+1) * 2^2006 + (2006^2 + 8*2006 + 20) = (2 * 2006+1) * 2^2006 + 2006^2 + 8*2006 + 20 := by linarith
    rw [l7] at l5
    have l8: ((2:ℤ) * 2006+1) * 2^2006 + 2006^2 + 8*2006 + 20 ≡ 36 [ZMOD 100] := by exact l5
    rw [a2006];
    exact l8





import Mathlib

/- Soit $P(x)=x^{4}-x^{3}-3 x^{2}-x+1$. Montrer qu'il existe une infinité d'entiers $n$ tels que $P\left(3^{n}\right)$ ne soit pas premier. -/
theorem number_theory_605280 (P : ℤ → ℤ) (hP : P = fun x => x^4 - x^3 - 3 * x^2 - x + 1) :
    ∀ N, ∃ n, n > N ∧ ¬ Prime (P (3^n)) := by
    -- Let $N \geqslant 1$. Let $x=3^{4 N+1}$,
    intro N
    use (4 * N + 1)
    constructor
    linarith
    -- We observe that $3^{2} \equiv-1(\bmod 5)$ and $3^{4} \equiv 1(\bmod 5)$.
    have h1 : 3 ^ 2 ≡ -1 [ZMOD 5] := rfl
    have h2 : 3 ^ 4 ≡ 1 [ZMOD 5] := rfl
    -- then $x=\left(3^{4}\right)^{N} \times 3 \equiv 3(\bmod 5)$, 
    have h3 : 3 ^ (4 * N + 1) ≡ 3 [ZMOD 5] := by
      rw [pow_add,pow_mul]
      have : (3 ^ 4) ^ N * 3 ^ 1 ≡ 1 ^ N * 3 ^ 1 [ZMOD 5] := by 
        refine Int.ModEq.mul ?_ rfl
        exact Int.ModEq.pow N h2
      simp at this
      simp [this]
    -- so $P(x) \equiv 3^{4}-3^{3}-3^{3}-3+1 \equiv 1+3+3-3+1 \equiv 0$ $(\bmod 5)$. 
    have h4 : P (3 ^ (4 * N + 1)) ≡ 0 [ZMOD 5] := by
      have h5 : 5 ∣ ((3:ℤ) ^ (4 * N + 1) - 3 ) := by 
        exact Int.dvd_sub_of_emod_eq h3
      rcases h5 with ⟨k,hk⟩
      have h6 : (3:ℤ) ^ (4 * N + 1) = 5 * k + 3 := 
        Eq.symm (add_eq_of_eq_sub (id (Eq.symm hk)))
      rw [hP,h6]
      simp
      ring_nf
      have : 25 + k * 310 + k ^ 2 * 1050 + k ^ 3 * 1375 + k ^ 4 * 625 = 5 * (5 + k * 62 + k ^ 2 * 210 + k ^ 3 * 275 + k ^ 4 * 125) := by ring
      rw [this]
      refine Dvd.dvd.modEq_zero_int ?_
      exact Int.dvd_mul_right 5 (5 + k * 62 + k ^ 2 * 210 + k ^ 3 * 275 + k ^ 4 * 125)
    -- On the other hand, $P(x)&gt;x^{4}-x^{3}-3 x^{3}-x^{3}=x^{3}(x-5)&gt;x-5&gt;3^{4 n}-5&gt;5$, 
    have h7 : ∀ x>5 , P x > x - 5 := by
      intro x hx
      have : P x > x ^ 4 - x ^ 3 - 3 * x ^ 3 - x ^ 3 := by 
        rw [hP] ;simp ;nlinarith
      have this' : x ^ 4 - x ^ 3 - 3 * x ^ 3 - x ^ 3 = x ^ 3 * (x - 5) := by ring
      have this' : x ^ 3 * (x - 5) > 1 * (x - 5) := by 
        refine Int.mul_lt_mul ?_ ?_ ?_ ?_ 
        refine one_lt_pow₀ (by linarith) (by simp)
        simp ;linarith
        refine pow_nonneg (by linarith) 3
      linarith
    by_cases h : N = 0
    · rw [hP,h] ;simp ;norm_num
    have h8 : 1 ≤ N := by omega
    have h9 : P (3 ^ (4 * N + 1)) > 5:= by
      have : 3 ^ (4 * 1 + 1) ≤ 3 ^ (4 * N + 1) := by apply Int.pow_le_pow_of_le_right ;simp ;omega
      have this' : 3 ^ (4 * N + 1) > (5:ℤ ) := by 
        have : 3 ^ (4 * 1 + 1) > 5 := by norm_num
        linarith
      specialize h7 (3 ^ (4 * N + 1)) this'
      have this' : 3 ^ (4 * N + 1) - 5 > (5:ℤ ) := by
        have : 3 ^ (4 * 1 + 1) > 10 := by norm_num
        linarith
      linarith
    have h10 : 5 ∣ P (3 ^ (4 * N + 1)) := by exact Int.dvd_of_emod_eq_zero h4
    rcases h10 with ⟨d,hd⟩
    have h11 : 1 < d := by
      by_contra!
      linarith
    rw [hd]
    have : ∃ n : ℕ, n = 5 * d := by refine CanLift.prf (5 * d) ?_ ;linarith
    rcases this with ⟨t,ht⟩
    by_contra!
    rw [← ht] at this
    have : Nat.Prime t := by exact Nat.prime_iff_prime_int.mpr this 
    have this' : ¬ Nat.Prime t := by
      apply Int.not_prime_of_int_mul ?_ ?_ ht.symm
      simp ;omega
    exact this' this
        
        
        
      
      
      
      
      


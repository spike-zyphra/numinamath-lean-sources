import Mathlib

/- Determine all integers $n \geqslant 1$ for which there exists a pair of positive integers $(a, b)$ such that no cube of a prime divides $a^{2}+b+3$ and  $$ \frac{a b+3 b+8}{a^{2}+b+3}=n $$ -/
theorem number_theory_24205 (n : ℕ) (hn : 1 ≤ n) :
    (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ (¬∃ p : ℕ, p.Prime ∧ p^3 ∣ a^2 + b + 3) ∧ ((a:ℝ) * b + 3 * b + 8) / (a^2 + b + 3) = n) ↔ n = 2 := by 

    --From left to right
    constructor
    intro h
    obtain ⟨a, b, apos, bpos, ⟨hp,hd⟩⟩ := h

    --As $b \equiv-a^{2}-3\left(\bmod a^{2}+b+3\right)$, the numerator of the given fraction satisfies $$ a b+3 b+8 \equiv a\left(-a^{2}-3\right)+3\left(-a^{2}-3\right)+8 \equiv-(a+1)^{3} \quad\left(\bmod a^{2}+b+3\right) $$.
    have cl1: (a^2+b+3) ∣ (a+1)^3 := by 
      have st: (a^2+b+3) ∣ (a*b+3*b+8) := by 
        use n
        norm_cast at hd
        field_simp at hd
        norm_cast at hd
        nth_rw 3 [mul_comm]
        exact hd
      zify at st
      have t2: ((a:ℤ)^2+b+3) ∣ ((a:ℤ)*(a^2+b+3)) := by
        use (a:ℤ)
        ring
      have t3: ((a:ℤ)^2+b+3) ∣ 3*((a:ℤ)^2+b+3) := by
        use 3
        ring
      have : ((a:ℤ)^2+b+3) ∣ ((a:ℤ)*(a^2+b+3)) - (a*b+3*b+8) := by exact Int.dvd_sub t2 st
      have tar: ((a:ℤ)^2+b+3) ∣ ((a:ℤ)*(a^2+b+3)) - (a*b+3*b+8) + 3*((a:ℤ)^2+b+3) := by
        exact Int.dvd_add this t3
      have : ((a:ℤ)*(a^2+b+3)) - (a*b+3*b+8) + 3*((a:ℤ)^2+b+3) = (a+1)^3 := by ring_nf
      rw [this] at tar
      norm_cast at tar

    -- As $a^{2}+b+3$ is not divisible by $p^{3}$ for any prime $p$, if $a^{2}+b+3$ divides $(a+1)^{3}$ then it does also divide $(a+1)^{2}$. 
    have cl2: (a^2+b+3) ∣ (a+1)^2 := by 
      let s := (a^2+b+3)
      let t := (a+1)
      rw [← Nat.factorization_le_iff_dvd]
      simp

      intro p
      by_cases pnp : ¬ Nat.Prime p
      have : s.factorization p = 0:= by
        exact Nat.factorization_eq_zero_of_non_prime s pnp
      linarith
      by_cases pnotd : ¬ p ∣ s
      have : s.factorization p = 0 := by exact Nat.factorization_eq_zero_of_not_dvd pnotd
      linarith

      have pdvd: p ∣ s := by push_neg at pnotd; exact pnotd
      have pp : Nat.Prime p := by push_neg at pnp; exact pnp

      rw [← Nat.factorization_le_iff_dvd] at cl1
      simp at cl1

      have : s.factorization p ≤ 2 := by  
        by_contra sfpnle2
        have sfpge3: 3 ≤ s.factorization p := by omega
        have : 3 ≤ multiplicity p s := by rw [Nat.multiplicity_eq_factorization]; exact sfpge3; exact pp; simp [s]
        push_neg at hp
        specialize hp p pp
        apply pow_dvd_of_le_multiplicity at this
        contradiction

      have : 1 ≤ (t).factorization p := by 
        have : 0 < s.factorization p := by
          apply Nat.Prime.factorization_pos_of_dvd
          exact pp; simp only [s]; nlinarith; exact pdvd
        by_contra l1
        have e0 : (t).factorization p = 0 := by omega
        have ll : s.factorization p ≤ (3*(t).factorization p) := by exact cl1 p
        have : (3*(t).factorization p) = 3*(t).factorization p := by exact rfl
        rw [this] at ll
        linarith
      field_simp
      nlinarith

      omega
      simp
      nlinarith
      simp

    --Since $$ 0&lt;(a+1)^{2}&lt;2\left(a^{2}+b+3\right) $$ we conclude $(a+1)^{2}=a^{2}+b+3$
    have cl3: (a^2+b+3) = (a+1)^2 := by 
      obtain ⟨k,hk⟩ := cl2
      have tmp : (a+1)^2 < 2 * (a^2+b+3) := by 
        have : (a+1)^2 = a^2 +2*a+1 := by ring
        rw [this]
        have : 2*a+1 < a^2 + 3 := by nlinarith
        linarith
      have : k < 2 := by nlinarith
      have : k ≠ 0 := by
        by_contra ke0
        rw [ke0] at hk
        ring_nf at hk
        have : 0 < 1+a*2 + a^2 := by omega
        linarith
      have : k = 1 := by omega
      rw [this] at hk
      rw [hk]
      ring
    
    --This yields $b=2(a-1)$ and $n=2$. 
    have cl4: (b:ℝ) = 2*((a:ℝ)-1) := by 
      rify at cl3
      ring_nf at cl3
      have : (b:ℝ) = 1 + ↑a * 2 + ↑a ^ 2 - ( 3 + ↑a ^ 2) := by linarith
      rw [this]
      field_simp
      ring
      
    rw [cl4] at hd
    ring_nf at hd
    field_simp at hd
    have : (a:ℝ) * 4 + ↑a ^ 2 * 2 + 2  = 2 *  (1 + ↑a * 2 + ↑a ^ 2) := by ring
    rw [this] at hd
    field_simp at hd
    norm_cast at hd
    norm_num at hd
    symm; exact hd


    --From right to left
    --The choice $(a, b)=(2,2)$ with $a^{2}+b+3=9$ shows that $n=2$ indeed is a solution.
    intro ne2
    use 2, 2
    simp [ne2]; 
    norm_num
    intro p hp
    by_contra p3d
    have ub: p^3 ≤ 9 := by apply Nat.le_of_dvd; norm_num; exact p3d
    have ubp : p ≤ 2 := by 
      by_contra pg2
      have : 3 ≤ p := by linarith
      have : 3^3 ≤ p^3 := by exact Nat.pow_le_pow_of_le_left this 3
      norm_num at this
      linarith
    have lbp : 2 ≤ p := by exact hp.two_le
    have pe2 : p = 2 := by linarith
    rw [pe2] at p3d
    norm_num at p3d
    

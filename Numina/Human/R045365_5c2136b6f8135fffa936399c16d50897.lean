import Mathlib

/- What is the maximum number of primes that divide both the numbers $n^3+2$ and $(n+1)^3+2$ where $n$ is a positive integer?

$ 
\textbf{(A)}\ 3
\qquad\textbf{(B)}\ 2
\qquad\textbf{(C)}\ 1
\qquad\textbf{(D)}\ 0
\qquad\textbf{(E)}\ \text{None of above}
$ -/
theorem number_theory_59461 :
    (∀n >0, Set.encard {p | p.Prime ∧ p ∣ n^3 + 2 ∧ p ∣ (n + 1)^3 + 2} ≤ 1) 
  ∧ (∃n >0, 0 < Set.encard {p | p.Prime ∧ p ∣ n^3 + 2 ∧ p ∣ (n + 1)^3 + 2}) 
    := by

    constructor

    intro n hn
    let S := {p | p.Prime ∧ p ∣ n^3 + 2 ∧ p ∣ (n + 1)^3 + 2}
    -- We will prove that if there is such a p, it can only be 109.
    have hS : S ⊆ {109} := by 
      intro p
      intro hp
      simp; simp [S] at hp
      obtain ⟨pp, h1, h2⟩ := hp

      let q : ℤ := (p:ℤ)
      let m : ℤ := (n:ℤ)

      have r1 : q ∣ m^3 + 2 := by simp [q,m]; exact Int.ofNat_dvd_left.mpr h1
      have r2 : q ∣ (m+1)^3 + 2 := by simp [q,m]; exact Int.ofNat_dvd_left.mpr h2
      have r3 : q ∣ 3*m^2 + 3*m + 1 := by 
        obtain ⟨t1,ht1⟩ := r1; obtain ⟨t2,ht2⟩ := r2
        use t2 - t1;
        linarith
      have r4 : q ∣ 2*m + 7 := by 
        obtain ⟨t2,ht2⟩ :=r2; obtain⟨t3,ht3⟩:= r3
        use 3*t2 - (m+2)*t3;
        nlinarith
      have r5 : q ∣ -15*m + 2 := by 
        obtain ⟨t3,ht3⟩ := r3; obtain ⟨t4, ht4⟩ := r4
        use 2*t3 - 3*m*t4;
        nlinarith
      have r6 : q ∣ 109 := by 
        obtain ⟨t4,ht4⟩ := r4;  obtain ⟨t5,ht5⟩ := r5
        use 15 * t4 + 2 * t5;
        nlinarith
      
      have pdvd: p ∣ 109 := by simp [q] at r6; norm_cast at r6
      have : Nat.Prime 109 := by norm_num
      rw [Nat.dvd_prime] at pdvd
      
      rcases pdvd with h | h
      rw [h] at pp; norm_num at pp
      assumption; norm_num
    
    have : S.encard ≤ 1 := by 
      refine Set.encard_le_one_iff.mpr ?_
      intro a b ha hb
      have : a=109 := by 
        have : a ∈ {109} := hS ha
        simp at this; exact this
      have : b=109 := by
        have : b ∈ {109} := hS hb
        simp at this; exact this
      linarith

    --For the second claim, we prove that if p = 109 and n=51, then 109 divides both numbers.
    simp [S] at this; assumption
    use 51;
    constructor; linarith
    simp;
    use 109
    simp
    constructor
    norm_num
    norm_num


import Mathlib

/- Find all solutions to the equation $\frac{1}{p} + \frac{1}{q} + \frac{1}{pq} = \frac{1}{n}$, where $p$ and $q$ are prime numbers and $n$ is a natural number. -/
theorem number_theory_2144 (p q n : ℕ) (hp : p.Prime) (hq : q.Prime):
    (1 / ((p:ℝ) * (q:ℝ)) + 1 / (p:ℝ) + 1 / (q:ℝ) = 1 / (n:ℝ)) ↔
    ((p = 2 ∧ q = 3 ∧ n = 1) ∨ (p = 3 ∧ q = 2 ∧ n = 1)) := by

      constructor

      --From left to right.
      have pge2: 2≤ p := by exact hp.two_le
      have qge2: 2≤ q := by exact hq.two_le
      have : 2 ≤ (p:ℝ) := by norm_cast;
      have : 2 ≤ (q:ℝ) := by norm_cast;

      --Rewrite the equation as (p - 1)(q- 1)n = pq - p - q + 1.
      intro h
      have eq : (p+q+1)*n = p*q := by 
        have : 4 ≤ (p:ℝ)*(q:ℝ) := by nlinarith
        have : n≠0 := by
          by_contra ne0
          rw [ne0] at h
          field_simp at h
          nlinarith
        field_simp at h
        have : (((p:ℝ) + p * q) * q + p * q * p) * n = (p*q)*(p+q+1)*n := by ring_nf
        rw [this] at h
        have : ((p:ℝ)*q) ≠ 0 := by nlinarith
        nth_rw 1 [mul_assoc] at h
        nth_rw 2 [mul_assoc] at h
        field_simp at h
        norm_cast at h
      
      --Then we have n ∣ pq, so n=p or n=q or n=1 or n = qp.
      have cn: n = 1 ∨ n = p ∨ n = q ∨ n = p * q := by 
        have : n ∣ p*q := by use p+q+1; linarith
        
        by_cases cnp : Nat.Coprime n p
        have : n ∣ q := by exact Nat.Coprime.dvd_of_dvd_mul_left cnp this
        have : n = 1 ∨ n = q := by exact (Nat.dvd_prime hq).mp this
        tauto
        have pdn: p ∣ n := by 
          rw [propext (Nat.Prime.dvd_iff_not_coprime hp)]; 
          rw [Nat.coprime_comm]; exact cnp
        obtain ⟨k, hk⟩ := pdn
        rw [hk] at this
        obtain ⟨i,hi⟩ := this
        have : k ∣ q := by use i; nlinarith
        have : k = 1 ∨ k = q := by exact (Nat.dvd_prime hq).mp this
        rcases this with k1 | kq
        rw [k1] at hk
        norm_num at hk
        tauto
        rw [kq] at hk
        tauto
      --n has to be 1, since otherwise n,p,q,pq do not satisfy the equation.
      have ne1: n = 1 := by 
        rcases cn with (cn|cn|cn|cn)
        exact cn
        exfalso; nlinarith
        exfalso; nlinarith
        exfalso; nlinarith
      --Then we have (p-1) * (q-1) = 2, so p=3, q=2 or p=2, q=3.
      have eq2: (p-1) * (q-1) = 2 := by
        rw [ne1] at eq
        norm_num at eq
        have exi1: ∃ pm1 : ℕ, pm1 + 1 = p := by use p-1; omega
        have exi2: ∃ qm1 : ℕ, qm1 + 1 = q := by use q-1; omega
        obtain ⟨pm1,hpm1⟩ := exi1
        obtain ⟨qm1,hqm1⟩ := exi2
        have : pm1*qm1 = 2 := by nlinarith
        have t1: pm1 = p - 1 := by omega
        have t2: qm1 = q - 1 := by omega
        rw [t1,t2] at this
        exact this

      have : 1 ≤ p-1 := by omega
      have : q-1 ≤ 2 := by nlinarith
      have : 1 ≤ q-1 := by omega

      by_cases qm1e1 : q-1=1
      
      rw [qm1e1] at eq2
      field_simp at eq2
      norm_num at eq2
      right
      norm_num at qm1e1
      tauto

      have qm1e2 : q-1=2 := by omega
      rw [qm1e2] at eq2
      field_simp at eq2
      have : p = 2 := by omega
      norm_num at qm1e2
      tauto


      --From right to left. Simple calculation.
      intro h
      rcases h with h | h
      simp [h]
      field_simp
      norm_num
      simp [h]
      field_simp
      norm_num


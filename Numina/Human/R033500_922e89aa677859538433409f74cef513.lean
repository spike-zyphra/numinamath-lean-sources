import Mathlib

/- ## Task A-2.3.

Determine all ordered triples $(m, n, p)$, where $m$ and $n$ are natural numbers, and $p$ is a prime number, for which


$$

(2 m+3)(4 n+1)=p m n

$$
 -/


theorem number_theory_213140 (m n p : ℕ) (hm : m > 0) (hn : n > 0)
    (hp : Nat.Prime p) :
    (2 * m + 3) * (4 * n + 1) = p * m * n ↔
    (m = 5 ∧ n = 1 ∧ p = 13) ∨ (m = 15 ∧ n = 1 ∧ p = 11) ∨ (m = 3 ∧ n = 3 ∧ p = 13) := by
--We split the proof in the "if part" and the "only if" part.
    constructor
--We first assume the equality holds, and solve the equation.
    · intro eq
--We will use the following lemmas: the gcd of 2m+3 and m is equal to the gcd of m and 3.
      have hgcd : gcd (2 * m + 3) m = m.gcd 3 := by
        rw [gcd_eq_nat_gcd]
        simp only [Nat.gcd_mul_right_add_left]
        rw [Nat.gcd_comm]
--3, 5 and 13 are prime.
      have prime3 : Nat.Prime 3 := by decide
      have prime5 : Nat.Prime 5 := by decide
      have prime13 : Nat.Prime 13 := by decide
--Since 3 is prime, then either m and 3 are coprime, or 3 divides m.
      have := Nat.coprime_or_dvd_of_prime prime3 m
      rcases this with h3 | h3
--We first consider the case where 3 does not divide m, so m and 3 are coprime, and thus m and 2m+3 are also coprime.
      · have : m.gcd 3 = 1 := by
          apply Nat.Coprime.isCoprime at h3
          rw [← Int.gcd_eq_one_iff_coprime] at h3
          zify
          rw_mod_cast [← h3]
          rw [Nat.gcd_comm]
        rw [this] at hgcd
--Similarly as above, we find that m divides 4n+1, with quotient α.
        have m_coprime : gcd m (2 * m + 3) = 1 := by
          rw [gcd_eq_nat_gcd]
          simp
          exact this
        have m_dvd : m ∣ (2 * m + 3) * (4 * n + 1) := by
          use p * n
          rw [eq]
          ring_nf
        rw [← dvd_gcd_mul_iff_dvd_mul, m_coprime, one_mul] at m_dvd
        obtain ⟨α,hα⟩ := m_dvd
--We also find that n divides 2m+3, with quotient β.
        have n_coprime : gcd n (4 * n + 1) = 1 := by
          rw [gcd_eq_nat_gcd]
          simp
        have n_dvd : n ∣ (2 * m + 3) * (4 * n + 1) := by
          use p * m
          rw [eq]
          ring_nf
        rw [← dvd_mul_gcd_iff_dvd_mul, n_coprime, mul_one] at n_dvd
        obtain ⟨β,hβ⟩ := n_dvd
        rw [hα, hβ, (by ring_nf : n * β * (m * α) = (α * β) * m * n)] at eq
        simp at eq
--We obtain that αβ=p, so either α=p and β=1, or α=1 and β=p.
        rcases eq with eq | nzero
        · rcases eq with eq | mzero
          · have : Nat.Prime (α * β) := by rw [eq]; exact hp
            rw [Nat.prime_mul_iff] at this
--If β=1, we obtain from the equations that m(p-8)=13. In particular, p-8 is either 1 or 13, both giving a contradiction with the fact that p is prime.
            rcases this with β1 | α1
            · rw [β1.2, mul_one] at hβ eq
              rw [eq, ← hβ] at hα
              ring_nf at hα
              zify at hα
              have new_eq : (m : ℤ) * ((p : ℤ) - 8) = 13 := by
                ring_nf
                rw [← hα]
                ring_nf
              have : (m : ℤ) * ((p : ℤ) - 8) > 0 := by rw [new_eq]; linarith
              have mcastpos : 0 < (m : ℤ) := by linarith
              rw [pos_iff_pos_of_mul_pos this] at mcastpos
              have pminus8_coe : (p : ℤ) - 8 = Int.ofNat (p - 8) := by
                simp only [Int.ofNat_eq_coe]
                rw [Int.natCast_sub]
                · ring_nf
                · linarith
              simp only [Int.ofNat_eq_coe] at pminus8_coe
              have new_eq_N : m * (p - 8) = 13 := by
                zify
                rw [← new_eq]
                simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
                left
                rw [← Int.toNat_sub_of_le]
                · simp [pminus8_coe]
                · linarith
              have : Nat.Prime (m * (p - 8)) := by rw [new_eq_N]; exact prime13
              rw [Nat.prime_mul_iff] at this
              rcases this with primem | m1
              · obtain ⟨primem,pminus8⟩ := primem
                have : p = 9 := by
                  rw [(by norm_num : 9 = 1 + 8)]
                  rw [← pminus8]
                  zify
                  rw [← pminus8_coe]
                  ring_nf
                rw [this] at hp
                contradiction
              · obtain ⟨primepminus8, m1⟩ := m1
                rw [m1, one_mul] at new_eq_N
                have : p = 21 := by
                  rw [(by norm_num : 21 = 13 + 8)]
                  rw [← new_eq_N]
                  zify
                  rw [← pminus8_coe]
                  ring_nf
                rw [this] at hp
                contradiction
--If α=1, we find that n(p-1)=5.
            · rw [α1.2, one_mul] at eq
              rw [α1.2, mul_one] at hα
              rw [eq, ← hα] at hβ
              ring_nf at hβ
              zify at hβ
              have new_eq : (n : ℤ) * ((p : ℤ) - 8) = 5 := by
                ring_nf
                rw [← hβ]
                ring_nf
              have : (n : ℤ) * ((p : ℤ) - 8) > 0 := by rw [new_eq]; linarith
              have ncastpos : 0 < (n : ℤ) := by linarith
              rw [pos_iff_pos_of_mul_pos this] at ncastpos
              have pminus8_coe : (p : ℤ) - 8 = Int.ofNat (p - 8) := by
                simp only [Int.ofNat_eq_coe]
                rw [Int.natCast_sub]
                · ring_nf
                · linarith
              simp only [Int.ofNat_eq_coe] at pminus8_coe
              have new_eq_N : n * (p - 8) = 5 := by
                zify
                rw [← new_eq]
                simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
                left
                rw [← Int.toNat_sub_of_le]
                · simp [pminus8_coe]
                · linarith
              have : Nat.Prime (n * (p - 8)) := by rw [new_eq_N]; exact prime5
--In particular, either n=5 and p-8=1, or n=1 and p-8=5. The first cases gives again a contradiction, since we find p=9.
              rw [Nat.prime_mul_iff] at this
              rcases this with primen | n1
              · obtain ⟨primen, pminus8⟩ := primen
                have : p = 9 := by
                  rw [(by norm_num : 9 = 1 + 8)]
                  rw [← pminus8]
                  zify
                  rw [← pminus8_coe]
                  ring_nf
                rw [this] at hp
                contradiction
--In the second case, we obtain p=13 and, substituting n=1, we also obtain m=5.
              · left
                obtain ⟨primepminus8, n1⟩ := n1
                rw [n1, one_mul] at new_eq_N
                rw [n1] at hα
                exact ⟨by linarith, by linarith, by linarith⟩
          · linarith
        · linarith
      
--We now assume that 3 divides m.
      · obtain ⟨k,hk⟩ := h3
        rw [hk] at eq
--We divide the equation by 3 to obtain (2k+1)(4n+1)=pmn.
        rw [(by ring_nf : (2 * (3 * k) + 3) * (4 * n + 1) = 3 * ((2 * k + 1) * ( 4 * n + 1))), (by ring_nf : p * (3 * k) * n = 3 * (p * k * n))] at eq
        simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at eq
--Since k is coprime to 2k+1, it must divide 4n+1. Let α be the quotient.
        have k_coprime : gcd k (2 * k + 1) = 1 := by
          rw [gcd_eq_nat_gcd]
          simp
        have k_dvd : k ∣ (2 * k + 1) * (4 * n + 1) := by
          use p * n
          rw [eq]
          ring_nf
        rw [← dvd_gcd_mul_iff_dvd_mul, k_coprime, one_mul] at k_dvd
        have kpos : k > 0 := by
          by_contra hlezero
          push_neg at hlezero
          simp only [nonpos_iff_eq_zero] at hlezero
          rw [hlezero, mul_zero] at hk
          linarith
        obtain ⟨α,hα⟩ := k_dvd
--Since n is coprime to 4n+1, it must divide 2k+1. Let β be the quotient.
        have n_coprime : gcd n (4 * n + 1) = 1 := by
          rw [gcd_eq_nat_gcd]
          simp
        have n_dvd : n ∣ (2 * k + 1) * (4 * n + 1) := by
          use p * k
          rw [eq]
          ring_nf
        rw [← dvd_mul_gcd_iff_dvd_mul, n_coprime, mul_one] at n_dvd
        obtain ⟨β,hβ⟩ := n_dvd
--We obtain that αβ=p is a prime, so one is 1 and the other is p.
        rw [hα, hβ, (by ring_nf : n * β * (k * α) = (α * β) * k * n)] at eq
        simp only [mul_eq_mul_right_iff] at eq
        rcases eq with eq | nzero
        · rcases eq with eq | kzero
          · have : Nat.Prime (α * β) := by rw [eq]; exact hp
            rw [Nat.prime_mul_iff] at this
            rcases this with β1 | α1
--If α=p and β=1, we obtain from the equations that k(p-8)=5.
            · rw [β1.2, mul_one] at eq hβ
              rw [eq, ← hβ] at hα
              ring_nf at hα
              zify at hα
              have new_eq : (k : ℤ) * ((p : ℤ) - 8) = 5 := by
                ring_nf
                rw [← hα]
                ring_nf
              have : (k : ℤ) * ((p : ℤ) - 8) > 0 := by rw [new_eq]; linarith
              have kcastpos : 0 < (k : ℤ) := by linarith
              rw [pos_iff_pos_of_mul_pos this] at kcastpos
              have pminus8_coe : (p : ℤ) - 8 = Int.ofNat (p - 8) := by
                simp only [Int.ofNat_eq_coe]
                rw [Int.natCast_sub]
                · ring_nf
                · linarith
              simp only [Int.ofNat_eq_coe] at pminus8_coe
              have new_eq_N : k * (p - 8) = 5 := by
                zify
                rw [← new_eq]
                simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
                left
                rw [← Int.toNat_sub_of_le]
                · simp [pminus8_coe]
                · linarith
              have : Nat.Prime (k * (p - 8)) := by rw [new_eq_N]; exact prime5
--Since k(p-8)=5 is a prime, then either k=5 and p-8=1, or k=1 and p-8=5.
              rw [Nat.prime_mul_iff] at this
              rcases this with primek | k1
--In the first case, we obtain p=9, contradicting the fact that p is prime.
              · obtain ⟨primek,pminus8⟩ := primek
                have : p = 9 := by
                  rw [(by norm_num : 9 = 1 + 8)]
                  rw [← pminus8]
                  zify
                  rw [← pminus8_coe]
                  ring_nf
                rw [this] at hp
                contradiction
--In the second case, we obtain p = 13 and, substituting k=1, we also obtain m=3 and n=3.
              · right; right
                rw [k1.2, Nat.cast_one, one_mul, (by norm_num : (5 : ℤ)= 13 - 8), sub_eq_sub_iff_sub_eq_sub, sub_self, sub_eq_zero] at new_eq
                have : p = 13 := by
                  zify
                  exact new_eq
                rw [k1.2, mul_one] at hβ
                ring_nf at hβ
                rw [k1.2, mul_one] at hk
                exact ⟨by linarith, by linarith, by linarith⟩
--Now, let us consider the case α=1 and β=p.
            · rw [α1.2, one_mul] at eq
              rw [α1.2, mul_one] at hα
              rw [← hα, eq] at hβ
              ring_nf at hβ
              zify at hβ
--We obtain the equation n(p-8)=3.
              have new_eq : (n : ℤ) * ((p : ℤ) - 8) = 3 := by
                ring_nf
                rw [← hβ]
                ring_nf
              have : (n : ℤ) * ((p : ℤ) - 8) > 0 := by
                rw [new_eq]
                linarith
              have ncastpos : 0 < (n : ℤ) := by linarith
              rw [pos_iff_pos_of_mul_pos this] at ncastpos
              have pminus8_coe : (p : ℤ) - 8 = Int.ofNat (p - 8) := by
                simp only [Int.ofNat_eq_coe]
                rw [Int.natCast_sub]
                · ring_nf
                · linarith
              simp only [Int.ofNat_eq_coe] at pminus8_coe
              have new_eq_N : n * (p - 8) = 3 := by
                zify
                rw [← new_eq]
                simp only [mul_eq_mul_left_iff, Nat.cast_eq_zero]
                left
                rw [← Int.toNat_sub_of_le]
                · simp [pminus8_coe]
                · linarith
--Since 3 is prime, then either n=3 and p-8=1, or n=1 and p-8=3.
              have : Nat.Prime (n * (p - 8)) := by rw [new_eq_N]; exact prime3
              rw [Nat.prime_mul_iff] at this
              rcases this with primen | n1
--In the first case we obtain again p=9, hence a contradiction.
              · obtain ⟨primen,pminus8⟩ := primen
                have : p = 9 := by
                  rw [(by norm_num : 9 = 1 + 8)]
                  rw [← pminus8]
                  zify
                  rw [← pminus8_coe]
                  ring_nf
                rw [this] at hp
                contradiction
--In the second case we find a solution, with p=11. Solving for m,n we find =1 and m=15.
              · right; left
                rw [n1.2, Nat.cast_one, one_mul, (by norm_num : (3 : ℤ)= 11 - 8), sub_eq_sub_iff_sub_eq_sub, sub_self, sub_eq_zero] at new_eq
                have : p = 11 := by
                  zify
                  exact new_eq
                exact ⟨by linarith, by linarith, by linarith⟩
          · linarith
        · linarith
--Conversely, if (m,n,p) is one of (5,1,13), (15,1,11) or (3,3,13), we can check that the equality holds.
    · intro h
      rcases h with h | h | h
      all_goals rw [h.1, h.2.1, h.2.2]
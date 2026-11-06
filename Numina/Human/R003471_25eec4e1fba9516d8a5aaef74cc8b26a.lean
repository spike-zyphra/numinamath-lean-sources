import Mathlib

/-
$12 \cdot 117$ Find all positive integers $m, n$ and prime $p$ such that $C_{m}^{2}-1=p^{n}$.
(Canadian Mathematical Olympiad Training Problem, 1992)
-/

theorem number_theory_186026 (m n p : ℕ) (mpos: 0 < m) (npos: 0 < n) (hp : Nat.Prime p):
  m.choose 2 - (1:ℤ) = p^n 
  ↔
  (m, n, p) = (3, 1, 2) ∨ (m, n, p) = (5, 2, 3) ∨ (m, n, p) = (8, 3, 3) ∨ 
  (m, n, p) = (4, 1, 5) := by 

  rw [Nat.choose_two_right]
  simp 
  clear npos
  constructor


  --From left to right.
  intro h
  by_cases hhh: m=1
  rw[hhh] at h
  have hhh1:↑p ^ n=(-1:ℤ):= by
    omega
  have hhh2:↑p ^ n≥ (0:ℤ):= by
    simp
  rw[hhh1] at hhh2
  trivial
  push_neg at hhh

  have h111 : 1< m := by
    omega

--We first observe that the given equation can be rewritten in two equivalent forms: $\frac{m(m-1)}{2}-1=p^n$ $\frac{(m+1)(m-2)}{2}=p^n$

  have h5:m-(1:ℤ)=↑(m-1):= by
    apply Eq.symm (Int.natCast_pred_of_pos ?_)
    omega
  have h1: 2∣m * ↑(m -  1) := by
    by_cases h2:m%2=0
    have h3: 2 ∣ m:= by
      exact Nat.dvd_of_mod_eq_zero h2
    exact Dvd.dvd.mul_right h3 (m - 1)
    push_neg at h2
    have h3: m % 2 = 1 := by omega
    have h4:2∣(m - 1):= by
      apply (Nat.modEq_iff_dvd' ?_).mp (id (Eq.symm h3))
      omega
    exact Dvd.dvd.mul_left h4 m
  have h3: ↑m * ↑(m - 1) / 2*2=↑m * ↑(m - 1):= by
    exact Nat.div_mul_cancel h1
  have h4: ↑m * ↑(m - 1) - (1:ℤ)*2 = ↑p ^ n*2:= by
    omega
  have h6: ↑m * ↑(m - 1) - (1:ℤ)*2=(m-(2:ℤ))*(m+(1:ℤ)):= by
    rw[← h5]
    ring_nf!
  rw[h6] at h4
  clear h
  clear h6
  clear h1
  have h2 :↑m - (2:ℤ) = ↑(m - 2):= by
    omega
  have h1: ↑m + (1:ℤ) = ↑(m+1):= by
    omega
  rw[h1] at h4
  rw[h2] at h4
  have h6: ↑p ^ n * (2:ℤ) =↑(p ^ n * 2):=by
    exact Eq.symm (Mathlib.Tactic.Ring.natCast_mul n rfl rfl)
  rw[h6] at h4
  have h:(m - 2) * (m + 1) = p ^ n * 2 := by
    exact Eq.symm ((fun {m n} => Int.ofNat_inj.mp) (id (Eq.symm h4)))
  clear h6
  clear h1
  clear h2
  clear h4
  clear h5
  clear h3

--(1) Suppose m is odd.  Since p is prime, there exists an integer t with 0≤t≤n such that $\frac{m+1}{2}=p^t$, $m-2=p^{n-t}$. Eliminating m gives $p^{n-t}+3=2p^t$

  by_cases h1 : 2 ∣ (m + 1)
  rw[dvd_def] at h1
  obtain ⟨u,hu⟩ := h1
  have hu1:= hu
  rw[hu] at h
  have h1: (m - 2) * u=p ^ n:= by
    nlinarith
  have h2: u∣p ^ n := by
    exact Dvd.intro_left (m - 2) h1
  rw[Nat.dvd_prime_pow] at h2
  have h3: (m - 2)∣p ^ n := by
    exact Dvd.intro u h1
  rw[Nat.dvd_prime_pow] at h3
  obtain ⟨l,hl⟩ := h2
  obtain ⟨t,ht⟩ := h3
  have hl1:= hl.left
  have hl2:= hl.right
  have ht1:= ht.left
  have ht2:= ht.right
  have h3: m=2+p^t := by
    exact (Nat.sub_eq_iff_eq_add' h111).mp ht2
  clear hl
  clear ht
  rw[h3] at hu
  rw[hl2] at hu
  have huu: p ^ t + 3 = 2 * p ^ l:= by
    omega

--If t=0 then $p^n+3=2$, no solution. Hence t>0. If n−t>0 then p must divide 3, so p=3, and $3^{n-t-1}+1=2·3^{t-1}$. If t−1>0 the right side is divisible by 3 but the left side is not, impossible.  If t−1=0 then $3^{n-t-1}+1=2$ so n−t−1=0, hence t=1, n=2, and m=3^{1}+2=5. If n−t=0 then $1+3=2p^t$ so p=2, n=t=1, and m=3.

  by_cases h4: l=0
  rw[h4] at huu
  rw[pow_zero] at huu
  have h5: p ^ t+1=0:= by
    omega
  have h6: p ^ t + 1 >0 := by 
    omega
  rw[h5] at h6
  trivial
  push_neg at h4
  have h5: l≥ 1 := by
    omega
  have h6: p ^ l=p^(l-1)*p^1:=by
    exact Eq.symm (Nat.pow_sub_mul_pow p h5)
  have h7: p ^ l=p^(l-1)*p:=by
    exact Eq.symm (Nat.pow_pred_mul h5)
  rw[h7] at huu
  rw[← mul_assoc] at huu
  have h8: p∣p ^ t + 3:= by
    exact Dvd.intro_left (2 * p ^ (l - 1)) (id (Eq.symm huu))
  by_cases h9: t=0
  rw[h9] at h8
  rw[pow_zero] at h8
  rw[show 1+3=4 by decide] at h8
  rw[dvd_def] at h8
  obtain⟨w,hw⟩ :=h8
  have h10: p≤ 4 := by
    by_cases h11: w=0
    rw[h11] at hw
    rw[mul_zero] at hw
    trivial
    push_neg at h11
    have h12: w ≥ 1:= by
      omega
    nlinarith
  interval_cases p
  rw[zero_mul] at hw
  trivial
  trivial
  by_cases h11: t=0
  rw[h11] at huu
  have h12: 2^(l-1)=2^0:= by 
    omega
  rw[pow_right_inj₀] at h12
  have h13: l=1 := by
    omega
  rw[h13] at hl2
  rw[show 2^1=2 by decide] at hl2
  rw[h11] at h3
  rw[show 2+2^0=3 by decide] at h3
  rw[h3] at h
  rw[hl2] at h
  have h14: 2^n=2^1:= by
    omega
  rw[pow_right_inj₀] at h14
  left
  constructor
  omega
  constructor
  omega
  decide
  decide
  decide
  decide
  decide
  push_neg at h11
  have h12: t≥ 1 := by 
    omega
  have h13:2∣ 2 ^ t + 3:= by
    omega
  have h14: 2^t=2^(t-1+1) := by
    exact False.elim (h11 h9)
  rw[pow_add] at h14
  rw[h14] at h13
  have h15: 2∣3 := by
    omega
  trivial
  have h11: 3∣ 4 := by
    omega
  trivial
  trivial
  push_neg at h9
  have h10: t≥ 1 := by
    omega
  clear h9
  have h11 : t=t-1+1 := by
    omega
  rw[h11] at h8
  rw[pow_add] at h8
  rw[pow_one] at h8
  have h12: p ∣ p ^ (t - 1) * p := by
    exact Nat.dvd_mul_left p (p ^ (t - 1))
  rw[Nat.dvd_add_right] at h8
  have h13:= h8
  rw[dvd_def] at h8
  obtain⟨w,hw⟩ :=h8
  have h10: p≤ 3 := by
    by_cases h11: w=0
    rw[h11] at hw
    rw[mul_zero] at hw
    trivial
    push_neg at h11
    have h12: w ≥ 1:= by
      omega
    nlinarith
  interval_cases p
  trivial
  trivial
  trivial
  clear h10
  have h14: t=t-1+1 := by
    omega
  rw[h14] at huu
  rw[pow_add] at huu
  have h15: 3 ^ (t - 1) + 1 = 2 * 3 ^ (l - 1) := by
    omega 
  by_cases h16: l=1
  rw[h16] at hl2
  rw[show 3^1=3 by decide] at hl2
  rw[h16] at hu
  have h17: 3^t=3^1:= by
    omega
  rw[h17] at ht2
  have h18: m=5:= by
    omega
  rw[h18] at h
  have h19: 3^n=3^2 := by
    omega
  rw[pow_right_inj₀] at h19
  right
  left
  constructor
  omega
  constructor
  omega
  decide
  decide
  decide
  push_neg at h16
  have h17: l≥ 2:= by 
    omega
  have h18: l-1=l-2+1:= by
    omega
  rw[h18] at h15
  rw[pow_add] at h15
  have h19: 3∣ 3 ^ (t - 1) + 1:=by
    omega
  by_cases h20 : t=1
  rw[h20] at h19
  rw[show 3^(1-1)+1=2 by decide] at h19
  trivial
  push_neg at h20
  have h21: t≥ 2:= by
    omega
  have h22: t-1=t-2+1 := by
    omega
  rw[h22] at h19
  rw[pow_add] at h19
  have h23:3 ∣ 3 ^ (t - 2) * 3 ^ 1:= by
    omega
  rw[Nat.dvd_add_right] at h19
  trivial
  exact h23
  exact h12
  exact hp
  exact hp
  push_neg at h1

--(2) Suppose m is even.  Again, since p is prime there is an integer t with 0≤t≤n such that $m+1=p^t$, $\frac{m-2}{2}=p^{n-t}$. Eliminating m gives $p^t−3=2p^{n-t}$.

  have h2: 2∣ m-2 := by 
    omega
  rw[dvd_def] at h2
  obtain ⟨u,hu⟩ := h2
  rw[hu] at h
  have hh: u * (m + 1) = p ^ n := by
    nlinarith
  have h2: u∣p ^ n := by
    exact Dvd.intro (m +1) hh
  rw[Nat.dvd_prime_pow] at h2
  have h3: (m +1)∣p ^ n := by
    exact Dvd.intro_left u hh
  rw[Nat.dvd_prime_pow] at h3
  obtain ⟨l,hl⟩ := h2
  obtain ⟨t,ht⟩ := h3
  have hl1:= hl.left
  have hl2:= hl.right
  have ht1:= ht.left
  have ht2:= ht.right
  clear hl
  clear ht
  have h3:3+2*p^l=p^t:= by
    omega

--Clearly t>0. If n−t>0 then p=3, and $3^{t-1}−1=2·3^{n-t-1}$ forces t−1=1 and n−t−1=0, so t=2, n=3, m=8. If n−t=0 then $p^t−3=2$ so p=5, t=n=1, and m=4. Therefore the only solutions in positive integers (m,n,p) are (3,1,2), (5,2,3), (8,3,3), (4,1,5).

  by_cases h4: l=0
  rw[h4] at h3
  rw[pow_zero] at h3
  have h5: p^t=5:= by 
    omega
  by_cases h6: t=0
  rw[h6] at h5
  rw[pow_zero] at h5
  trivial
  push_neg at h6
  have h7: t=t-1+1 := by
    omega
  rw[h7] at h5
  rw[pow_add] at h5
  rw[pow_one] at h5
  have h8: p∣ 5:= by
    exact Dvd.intro_left (p ^ (t - 1)) h5
  have h9:= h8
  rw[dvd_def] at h8
  obtain ⟨w,hw⟩ := h8
  have h10: p≤ 5 := by
    by_cases h11: w=0
    rw[h11] at hw
    rw[mul_zero] at hw
    trivial
    push_neg at h11
    have h12: w ≥ 1:= by
      omega
    nlinarith 
  interval_cases p 
  trivial
  trivial
  trivial
  trivial
  trivial
  have h11: 5 ^ (t - 1) = 5^0 := by
    omega
  rw[pow_right_inj₀] at h11
  have h12:t=1:= by
    omega
  rw[h12] at ht2
  have h13: m=4 := by
    omega
  rw[h4] at hl2
  rw[hl2] at hh
  rw[h13] at hh
  have h14: 5^n=5^1 := by
    omega
  rw[pow_right_inj₀] at h14
  right
  right
  right
  constructor
  exact h13
  constructor
  exact h14
  decide
  decide
  decide
  decide
  decide
  push_neg at h4
  have h5: l=l-1+1 := by
    omega
  by_cases h6: t=0
  rw[h6] at h3
  rw[pow_zero] at h3
  have h7:1≥ 3:= by
    omega
  trivial
  push_neg at h6
  have h7: t=t-1+1 := by
    omega
  rw[h5] at h3
  rw[h7] at h3
  rw[pow_add] at h3
  rw[pow_add] at h3
  rw[pow_one] at h3
  have h8: p∣  3 + 2 * (p ^ (l - 1) * p) := by
    exact Dvd.intro_left (p ^ (t - 1)) (id (Eq.symm h3))
  have h9: p∣2 * (p ^ (l - 1) * p) := by
    rw[← mul_assoc]
    exact Nat.dvd_mul_left p (2 * p ^ (l - 1))
  rw[Nat.dvd_add_left] at h8
  clear h9
  have h9:= h8
  rw[dvd_def] at h8
  obtain ⟨w,hw⟩ := h8
  have h10: p≤ 3 := by
    by_cases h11: w=0
    rw[h11] at hw
    rw[mul_zero] at hw
    trivial
    push_neg at h11
    have h12: w ≥ 1:= by
      omega
    nlinarith 
  interval_cases p
  rw[zero_mul] at hw
  trivial
  trivial
  trivial
  have h11: 1 + 2 * 3 ^ (l - 1)  = 3 ^ (t - 1) := by
    omega
  by_cases h12: t-1=0
  rw[h12] at h11
  have h13 :2 * 3 ^ (l - 1) =0:= by
    omega
  have h14 :2 * 3 ^ (l - 1) >0:= by
    exact Nat.pos_of_neZero (2 * 3 ^ (l - 1))
  rw[h13] at h14
  trivial
  push_neg at h12
  have h13: t-1=t-2+1:= by
    omega
  rw[h13] at h11
  rw[pow_add] at h11
  by_cases h14: l-1=0
  rw[h14] at h11
  have h15: 3^(t-2)=3^0 := by
    omega
  rw[pow_right_inj₀] at h15
  have h16: t=2 := by
    omega
  rw[h16] at ht2
  have h17: m=8 :=by
    rw[show 3^2=9 by decide] at ht2
    omega
  rw[h16] at h3
  have h18: 3^(l-1)=3^0:= by
    omega
  rw[pow_right_inj₀] at h18
  have h19: l=1 := by
    omega
  rw[h19] at hl2
  rw[hl2] at hh
  rw[h17] at hh
  have h20: 3^n=3^3:= by
    omega
  rw[pow_right_inj₀] at h20
  right
  right
  left
  constructor
  exact h17
  constructor
  exact h20
  decide
  decide
  decide
  decide
  decide
  decide
  decide
  push_neg at h14
  have h15: l-1=l-2+1 := by
    omega
  rw[h15] at h11
  rw[pow_add] at h11
  have h16: 3∣1 + 2 * (3 ^ (l - 2) * 3 ^ 1) := by
    omega
  have h17: 3∣2 * (3 ^ (l - 2) * 3 ^ 1) := by
    omega
  have h18: 3∣ 1 := by
    omega
  trivial
  exact h9
  exact hp
  exact hp



  --From right to left, simple verification.
  intro h
  rcases h with ⟨me,ne,pe⟩ | ⟨me,ne,pe⟩ | ⟨me,ne,pe⟩ | ⟨me,ne,pe⟩ <;>
  simp [me,ne,pe]
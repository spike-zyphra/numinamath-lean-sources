import Mathlib

/-
Solve the equation $3^{x}+4^{y}=5^{z}$ in natural numbers.

#
-/

--We first have the following easy lemmas used later.
lemma p1 (a b : ℕ) (h : b≤ a): (a + b) - (a - b) = b + b := by
   omega

lemma p2 (a b : ℕ) (h : a∣ 2^b): ∃(j:ℕ), j≤ b∧ a=2^j:= by
  have h: a∈ (2^b).divisors:= by
    rw[Nat.mem_divisors]
    constructor
    exact h
    exact Ne.symm (NeZero.ne' (2 ^ b))
  rw[Nat.mem_divisors_prime_pow] at h
  exact h
  decide

lemma p3 (a b : ℕ) (h : a∣ 3^b): ∃(j:ℕ), j≤ b∧ a=3^j:= by
  have h1: a∈ (3^b).divisors:= by
    rw[Nat.mem_divisors]
    constructor
    exact h
    exact Ne.symm (NeZero.ne' (3 ^ b))
  rw[Nat.mem_divisors_prime_pow] at h1
  exact h1
  decide

lemma p4 (a b c d: ℕ) (h1: a=3^b) (h2: c=3^d) (h3:c=a+2): c=3∧a=1:= by
  rw[h1] at h3
  rw[h2] at h3
  by_cases h5: b=0
  rw[h5] at h1
  rw[h5] at h3
  rw[h3] at h2
  rw[show 3^0+2=3 by decide] at h2
  rw[show 3^0=1 by decide] at h1
  constructor
  exact h2
  exact h1
  push_neg at h5
  have h4 : 3 ^ d%3 =(3 ^ b + 2)%3:= by
    rw[h3]
  rw[Nat.pow_mod] at h4
  rw[show 3%3=0 by decide] at h4
  rw[zero_pow] at h4
  rw[show 0%3=0 by decide] at h4
  rw[Nat.add_mod] at h4
  rw[Nat.pow_mod] at h4
  rw[show 3%3=0 by decide] at h4
  rw[zero_pow] at h4
  rw[show 0%3=0 by decide] at h4
  rw[show (0 + 2 % 3) % 3=2 by decide] at h4
  trivial
  trivial
  by_contra h6
  rw[← h2] at h3
  rw[h6] at h2
  rw[show 3^0=1 by decide] at h2
  rw[h2] at h3
  have : 0 ≤ 3^b := by exact Nat.zero_le (3 ^ b)
  linarith

--Theorem Let $x,y,z$ be nonnegative integers satisfying $3^x+4^y=5^z$. Then the only solution is $(x,y,z)=(2,2,2)$

theorem number_theory_200378 (x y z : ℕ) (h : 3^x + 4^y = 5^z)(xne0: x≠0)(yne0: y≠0)(zne0: z≠0) : (x, y, z) = (2, 2, 2) := by 

--1. First reduce the equation modulo $3$.  Since $4^y \equiv 1 \pmod3$, $3^x \equiv 0\pmod3$, we have $3^x + 4^y \equiv 1 \pmod3$, and hence $5^z = 3^x + 4^y \equiv (-1)^z \pmod3$. It follows that $(-1)^z\equiv 1\pmod3$, so $z$ is even.  Write $z=2u$.

  have h1 : (3^x + 4^y)%3 = 5^z%3:= by
    rw[h]

  have h2 : (x≠ 0) → 1 = 2^z%3:= by 
    intro h3
    rw[Nat.add_mod] at h1
    rw[Nat.pow_mod] at h1
    rw[Nat.mod_self] at h1
    rw[zero_pow] at h1
    have hh : (0 : ℕ) < 3 := by decide
    rw[Nat.mod_eq_of_lt hh] at h1
    rw[zero_add] at h1
    rw[Nat.pow_mod] at h1
    clear hh
    have hh : 4%3=1 := by decide
    rw[hh] at h1
    clear hh
    rw[one_pow] at h1
    have hh : 1%3%3=1 := by decide
    rw[hh] at h1
    clear hh
    rw[Nat.pow_mod] at h1
    have hh : 5%3=2 := by decide
    rw[hh] at h1
    exact h1
    exact h3

  have h4 :z%2=0:= by
    have aa:x≠ 0:= by
      exact xne0
    apply h2 at aa
    by_cases hh : z % 2=0
    exact hh
    have h4:z%2=1:= by
      have hlt : z % 2 < 2 := Nat.mod_lt z (by decide)
      have (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 := by
        interval_cases n
        · exact Or.inl rfl
        · exact Or.inr rfl
      apply this at hlt
      rcases hlt with hlt1|hlt2
      apply hh at hlt1
      trivial
      exact hlt2
    clear hh
    have hrt : 2 = 2 ^ z % 3 := by
      have : Odd z := by exact Nat.odd_iff.mpr h4
      obtain ⟨k,hk⟩ := this
      rw [hk]
      rw [pow_succ]
      simp [Nat.mul_mod]
      rw [pow_mul]
      norm_num
      rw [Nat.mul_mod]
      rw [Nat.pow_mod]
      simp
    rw[← aa] at hrt
    trivial
  clear h1

--2. Next reduce modulo $4$.  We have $5^z - 3^x = 4^y$, and $5^z \equiv 1^z \equiv 1 \pmod4$, $3^x \equiv (-1)^x \pmod4$, so $5^z - 3^x \equiv 1 - (-1)^x \equiv 0\pmod4$,which forces $(-1)^x = 1$, hence $x$ is even.  Write $x=2v$.

  have h5 :x%2=0:= by
      have aa:y≠ 0:= by
        exact yne0
      have h2 : (3^x + 4^y)%4 = 5^z%4:= by
        rw[h]
      rw[Nat.add_mod] at h2
      rw[Nat.pow_mod] at h2
      rw[Nat.pow_mod 4] at h2
      rw[Nat.pow_mod 5] at h2
      rw[Nat.mod_self] at h2
      rw[zero_pow] at h2
      rw [show 5%4 = 1 by decide] at h2
      rw [show 3%4 = 3 by decide] at h2
      rw [show 0%4 = 0 by decide] at h2 
      rw[add_zero] at h2
      rw[one_pow] at h2
      rw[show 1%4 = 1 by decide] at h2
      rw[Nat.mod_eq_of_lt] at h2
      by_cases hh : x%2=0
      exact hh
      have h4:x%2=1:= by
        have hlt : x % 2 < 2 := Nat.mod_lt x (by decide)
        have (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 := by
          interval_cases n
          · exact Or.inl rfl
          · exact Or.inr rfl
        apply this at hlt
        rcases hlt with hlt1|hlt2
        apply hh at hlt1
        trivial
        exact hlt2
      clear hh
      have hrt : 3 ^ x % 4 = 3 := by
        have : Odd x := by exact Nat.odd_iff.mpr h4
        obtain ⟨k,hk⟩ := this
        rw [hk]
        rw [pow_succ]
        rw [pow_mul]
        rw [Nat.mul_mod]
        rw [Nat.pow_mod]
        simp
      rw[h2] at hrt
      trivial
      have hhh: 4>0 := by decide
      have hh: 3 ^ x % 4 < 4:= by
        exact Nat.mod_lt (3 ^ x) hhh
      exact hh
      exact aa
  clear h2

  have uu: Even z := by
    exact Nat.even_iff.mpr h4
  obtain ⟨u,hu⟩:=uu
  replace hu : z = 2 * u := by omega

  have vv: Even x := by
    exact Nat.even_iff.mpr h5
  obtain ⟨v,hv⟩:=vv
  replace hv : x = 2 * v := by omega

  have h6: 2^(2*y)=(5^u-3^v)*(5^u+3^v)∧ 3^v≤ 5^u:= by
    rw[hu] at h
    rw[hv] at h
    rw[show 4=2^2 by decide] at h
    rw[← pow_mul] at h
    symm at h
    rw[add_comm] at h
    have hhhh: 5 ^ (2 * u)  = 2 ^ (2 * y) + 3 ^ (2 * v):= by
      exact h
    have hhh: 0≤ 2 ^ (2 * y):= by
      exact Nat.zero_le (2 ^ (2 * y))
    have hh: 3 ^ (2 * v) ≤ 5 ^ (2 * u):=by
      linarith
    rw[← Nat.sub_eq_iff_eq_add hh] at h
    symm at h
    rw[mul_comm 2 u] at h
    rw[mul_comm 2 v] at h
    rw[pow_mul 5 u 2] at h
    rw[pow_mul 3 v 2] at h
    rw[Nat.sq_sub_sq] at h
    rw[mul_comm (5 ^ u + 3 ^ v)] at h
    rw[mul_comm 2 v] at hh
    rw[mul_comm 2 u] at hh
    rw[pow_mul] at hh
    rw[pow_mul] at hh
    have hhhhh: (3 ^ v)  ≤ (5 ^ u) := by
      by_contra xx
      push_neg at xx
      have xyz: 2≠ 0 := by decide
      apply Nat.pow_lt_pow_left at xx
      apply xx at xyz
      linarith
    exact And.intro h hhhhh 
  clear h4
  clear h5
  have h1:= h6.left
  have h2:= h6.right
  clear h6

--3. Now the equation becomes $4^y=5^{2u}-3^{2v} \rightarrow 2^{2y}=(5^u-3^v)(5^u+3^v). Both factors on the right are powers of $2$.  Set $5^u - 3^v = 2^k$, $5^u + 3^v = 2^l$, with $k,l≥ 0$ and $k+l=2y$.

  have h1: ∃ (k: ℕ), ∃ (l: ℕ), k+l=2*y ∧ 5^u-3^v=2^k ∧ 5^u+3^v=2^l ∧ l>k:= by 
    have h5: (5 ^ u - 3 ^ v)∣ 2 ^ (2 * y) := by
      rw[dvd_def]
      use (5 ^ u + 3 ^ v)

    have h6: (5 ^ u + 3 ^ v)∣ 2 ^ (2 * y) := by
      rw[dvd_def]
      use (5 ^ u - 3 ^ v)
      rw[mul_comm (5 ^ u + 3 ^ v)]
      exact h1
    apply p2 at h5
    apply p2 at h6
    obtain ⟨k,hk⟩:= h5
    obtain ⟨l,hl⟩:= h6
    use k
    use l
    have hk1:=hk.left
    have hk2:=hk.right
    have hl1:=hl.left
    have hl2:=hl.right
    clear hl
    clear hk
    constructor
    rw[hk2] at h1
    rw[hl2] at h1
    rw[← pow_add] at h1
    rw[pow_right_inj₀] at h1
    symm at h1
    exact h1
    decide
    decide
    constructor
    exact hk2
    constructor
    exact hl2
    have h5: 5 ^ u - 3 ^ v<5 ^ u + 3 ^ v:= by
      refine Nat.sub_lt_left_of_lt_add h2 ?_
      have : 0 < 3 ^ v := by exact Nat.pos_of_neZero (3 ^ v)
      linarith
    rw[hk2] at h5
    rw[hl2] at h5
    rw[pow_lt_pow_iff_right₀] at h5
    exact h5
    decide
  obtain ⟨k,l,h1⟩:=h1
  have h11:=h1.left
  have h12:=h1.right.left
  have h13:=h1.right.right.left
  have h14:=h1.right.right.right
  clear h1

--4. Then $5^u = \frac{2^k+2^l}{2}$, $3^v = \frac{2^l-2^k}{2}$.

  have h12': 2*5^u=2^l+2^k:= by
    have hhh: (5 ^ u - 3 ^ v)+(5 ^ u + 3 ^ v)=2 ^ k+2^l := by
      rw[h12]
      rw[h13]
    rw[add_comm (5^u) (3^v)] at hhh
    rw[← add_assoc] at hhh
    rw[Nat.sub_add_cancel h2] at hhh
    rw[← two_mul] at hhh
    rw[add_comm] at hhh
    exact hhh

  have h13': 2*3^v=2^l-2^k:= by
    have hhh: (5 ^ u + 3 ^ v)-(5 ^ u - 3 ^ v) = 2 ^ l-2^k := by
      rw[h12]
      rw[h13]
    rw[p1] at hhh
    rw[← two_mul] at hhh
    exact hhh
    exact h2
  clear h12
  clear h13

  have h3: 2^k ∣ 2^l+2^k := by
    have h4: 2^k ∣ 2^l := by
      apply (Nat.pow_dvd_pow_iff_le_right ?_).mpr 
      exact Nat.le_of_succ_le h14
      decide
    have h5: 2^k ∣ 2^k := by
      exact Nat.dvd_refl (2 ^ k)
    exact dvd_add h4 h5

-- 5. Since $l>k$, $2^l$ is divisible by $4$ but $2^k$ is not, so $k=1$.  Hence $3^v = 2^{l-1}-1$.

  have h4: k=1:= by
    rw[← h12'] at h3
    by_cases h4: k=0
    rw[h4] at h13'
    rw[show 2^0=1 by decide] at h13'
    have h5: 2 * 3 ^ v+1=2 ^ l := by
      apply Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add h).mp) ?_ (id (Eq.symm h13')))
      exact Nat.one_le_two_pow
    have h6: (2 * 3 ^ v + 1)%2 = 2 ^ l%2 := by
      rw[h5]
    rw[Nat.add_mod] at h6
    rw[Nat.mul_mod] at h6
    rw[Nat.pow_mod 2 l] at h6
    repeat rw[show 2%2=0 by decide] at h6
    rw[zero_mul] at h6
    repeat rw[show 0%2=0 by decide] at h6
    rw[zero_add] at h6
    rw[zero_pow] at h6
    repeat rw[show 0%2=0 by decide] at h6
    rw[show 1%2=1 by decide] at h6
    trivial
    by_contra aa
    rw[aa] at h5
    rw[show 2^0=1 by decide] at h5
    have h7: 2 * 3 ^ v=0 := by
      exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (id (Eq.symm h5)))
    have h8: 2 * 3 ^ v≠ 0 := by
      exact Ne.symm (NeZero.ne' (2 * 3 ^ v))
    apply h8 h7
    by_cases h5: k>1
    have h6:4∣2^k:= by
      apply (Nat.dvd_prime_pow ?_).mpr ?_
      decide
      use 2
      constructor
      exact h5
      decide
    have h7: 4∣ 2*5^u := by
      exact dvd_trans h6 h3
    push_neg at h4
    have h8: k≠ 1 := by
      exact Ne.symm (Nat.ne_of_lt h5)
    by_contra h9
    clear h9
    rw[dvd_def] at h7
    obtain ⟨t,ht⟩ := h7
    have h9: 5^u=2*t := by
      rw[show 4=2*2 by decide] at ht
      rw[mul_assoc] at ht
      rw[Nat.mul_left_cancel_iff] at ht
      exact ht
      decide
    have h10: 5^u%2=2*t%2 := by
      rw[h9]
    rw[← Nat.mod_mul_mod] at h10
    rw[Nat.pow_mod] at h10
    rw[show 2%2=0 by decide] at h10
    rw[show 5%2=1 by decide] at h10
    rw[one_pow] at h10
    rw[zero_mul] at h10
    rw[show 1%2=1 by decide] at h10
    rw[show 0%2=0 by decide] at h10
    trivial
    push_neg at h4
    push_neg at h5
    rw[Nat.le_one_iff_eq_zero_or_eq_one] at h5
    rcases h5 with h5|h5
    apply h4 at h5
    trivial
    exact h5
  clear h3
  rw[h4] at h14
  rw[h4] at h12'
  rw[h4] at h13'
  rw[h4] at h11
  rw[show 2^1=2 by decide] at h12'

  have h3:3^v=2^(l-1)-1 := by
    have h5: l=l-1+1 := by
      apply (Nat.sub_eq_iff_eq_add ?_).mp rfl
      exact Nat.one_le_of_lt h14
    rw[h5] at h13'
    rw[pow_add] at h13'
    nth_rewrite 2 [show 2^1=1*2 by decide] at h13'
    rw[show 2^1=2 by decide] at h13'
    rw[mul_comm] at h13'
    have h6: 3 ^ v * 2 +1 * 2= 2 ^ (l - 1) * 2:= by
      apply Eq.symm ((fun {b a c} h => (Nat.sub_eq_iff_eq_add h).mp) ?_ (id (Eq.symm h13')))
      apply Nat.mul_le_mul_right 2 ?_
      exact Nat.one_le_two_pow
    have h7: 3 ^ v +1 = 2 ^ (l - 1) := by
      rw[← add_mul] at h6
      apply Nat.mul_right_cancel at h6
      exact h6
      decide
    have h8: 3 ^ v= 2 ^ (l - 1)-1:= by
      exact Nat.eq_sub_of_add_eq h7
    exact h8


--6. Write $l-1=2s$.  Then $3^v = (2^s-1)(2^s+1)$, a product of two powers of $3$ differing by $2$, which forces these factors to be $1$ and $3$.  Thus $s=1$, $l=3$, and $k+l = 1+3 = 4 = 2y$, so $y=2$.

  have h6: l-1=2*y-1-1 := by
    apply Nat.eq_sub_of_add_eq' at h11
    exact congrFun (congrArg HSub.hSub h11) 1
  
  have h7: l-1=2*y-2 := by
    exact h6
  clear h6

  have h8: 2∣ 2*y-2 := by
    apply Nat.dvd_sub ?_ ?_
    norm_num
    omega
    use y
  rw[← h7] at h8
  rw[dvd_def] at h8
  obtain ⟨w,hw⟩ :=h8
  rw[hw] at h3
  rw[show 1=1^2 by decide] at h3
  rw[mul_comm] at h3
  rw[pow_mul] at h3
  rw[Nat.sq_sub_sq] at h3

  have h5: (2^w+1)∣ 3^v := by
      rw[dvd_def]
      use (2^w-1)

  have h6: (2^w-1)∣ 3^v := by
    rw[dvd_def]
    use (2^w+1)
    rw[mul_comm (2^w-1)]
    exact h3
  apply p3 at h5
  apply p3 at h6
  obtain ⟨i,hi⟩:= h5
  obtain ⟨j,hj⟩:= h6
  have hi1:=hi.left
  have hi2:=hi.right
  have hj1:=hj.left
  have hj2:=hj.right
  clear hi
  clear hj

  have h8: (2 ^ w + 1)=3 ∧ (2 ^ w - 1)=1 := by
    have h9: 2 ^ w + 1=2 ^ w - 1+2 := by 
      apply Nat.add_left_inj.mpr ?_
      exact Eq.symm (succ_mersenne w)
    exact p4 (2 ^ w - 1) (j) (2^w+1) (i) hj2 hi2 h9
  
  have h81:=h8.left
  have h82:=h8.right
  clear h8
  have h9: 2^w=2:= by
    exact Eq.symm ((fun {a b} => Nat.succ_inj.mp) (id (Eq.symm h81)))
  
  nth_rewrite 2 [show 2=2^1 by decide] at h9
  have h10: w=1:= by
    rw[pow_right_inj₀] at h9
    exact h9
    decide
    decide
  clear h9
  clear h81
  clear h82
  clear hj2
  clear hi2
  rw[h10] at hw

  have hw1: l=3:= by
    exact Nat.pred_eq_succ_iff.mp hw
  clear hw
  rw[hw1] at h11
  clear h7
  rw[show 1+3=2*2 by decide] at h11
  rw[Nat.mul_left_cancel_iff] at h11
  symm at h11

--7. Therefore $x=2$, $y=2$, $z=2$, and no other solution is possible.

  rw[h10] at h3
  rw[show (2 ^ 1 + 1) * (2 ^ 1 - 1)=3^1 by decide] at h3

  have h31: v=1:= by
    rw[pow_right_inj₀] at h3
    exact h3
    decide
    decide
  clear h3
  clear hj1
  clear hi1
  clear h13'
  rw[hw1] at h12'
  rw[show 2^3+2=2*5^1 by decide] at h12'
  rw[Nat.mul_left_cancel_iff] at h12'
  rw[pow_right_inj₀] at h12'
  rw[h12'] at hu
  rw[show 2*1=2 by decide] at hu
  rw[h31] at hv
  rw[show 2*1=2 by decide] at hv
  simp
  constructor
  exact hv
  constructor
  exact h11
  exact hu
  decide
  decide
  decide
  decide
import Mathlib 

/-Trouver tous les entiers $\boldsymbol{n} \geqslant 1$ tels que $2^{n}+12^{n}+2014^{n}$ soit un carré parfait.-/
theorem number_theory_607518 : {n | 1 ≤ n ∧ IsSquare (2^n + 12^n + 2014^n) } = ∅ := by 
  ext n
  simp
  intro hn isSq 
  -- Regardons l'expression modulo $3: 2^{\mathfrak{n}}+12^{n}+2014^{n} \equiv(-1)^{n}+1 \bmod 3$.
  have h1 : 2 ^ n + 12 ^ n + 2014 ^ n ≡ (-1)^n + 1 [ZMOD 3] := by 
    have h11 := Int.ModEq.pow n (show 2 ≡ -1 [ZMOD 3] by rfl)
    have h12 := Int.ModEq.pow n (show 12 ≡ 0 [ZMOD 3] by rfl)
    have h13 := Int.ModEq.pow n (show 2014 ≡ 1 [ZMOD 3] by rfl)
    convert Int.ModEq.add (Int.ModEq.add h11 h12) h13 using 1
    norm_num
    omega
  -- Comme un carré n'est jamais congru à 2 modulo 3, on en déduit que $n$ est impair.
  have oddn : Odd n := by 
    have h2 (n : ℕ) (hn : IsSquare n) : ¬ n ≡ 2 [ZMOD 3] := by 
      obtain ⟨r, hr⟩ := hn 
      intro nmod3
      mod_cases e : (r : ℤ) % 3 <;> simp [hr] at nmod3 
      <;> replace e := Int.ModEq.mul e e <;> have := e.symm.trans nmod3 
      <;> simp at this <;> tauto
    by_contra! evencase
    simp [Nat.not_odd_iff_even] at evencase
    simp [(neg_one_pow_eq_one_iff_even _).2 evencase] at h1 
    exact h2 (2^n + 12^n + 2014^n) isSq (by convert h1; simp)
  -- Regardons ensuite l'expression modulo 7 :
  -- $$
  -- 2^{n}+12^{n}+2014^{n} \equiv 2^{n}+(-2)^{n}+5^{n} \equiv 5^{n} \quad \bmod 7
  -- $$
  have h2 : 2 ^ n + 12 ^ n + 2014 ^ n ≡ 5^n [ZMOD 7] := by 
    have h21 := Int.ModEq.pow n (show 2 ≡ 2 [ZMOD 7] by rfl)
    have h22 := Int.ModEq.pow n (show 12 ≡ -2 [ZMOD 7] by rfl)
    have h23 := Int.ModEq.pow n (show 2014 ≡ 5 [ZMOD 7] by rfl)
    convert Int.ModEq.add (Int.ModEq.add h21 h22) h23 using 1
    rw [Odd.neg_pow oddn 2]
    ring 
  
  have h3 (n : ℕ) (hn : IsSquare n) : n ≡ 0 [ZMOD 7] ∨ n ≡ 1 [ZMOD 7] 
    ∨ n ≡ 2 [ZMOD 7] ∨ n ≡ 4 [ZMOD 7] := by 
      obtain ⟨r, hr⟩ := hn 
      simp [hr]
      mod_cases e : (r : ℤ) % 7 <;> replace e := Int.ModEq.mul e e <;> simp at e <;> tauto
  
  -- car $n$ est impair. Lorsque $n$ est impair, $5^{n}$ ne peut être congru qu'à 3,5 ou 6 modulo 7 . 
  have h4 : 5^n ≡ 3 [ZMOD 7] ∨ 5^n ≡ 5 [ZMOD 7] ∨ 5^n ≡ 6 [ZMOD 7]:= by
    obtain ⟨k, hk⟩ := oddn 
    have : 5^(2 * k) ≡ 0 [ZMOD 7] ∨ 5^(2 * k) ≡ 1 [ZMOD 7] ∨ 5^(2 * k) ≡ 2 [ZMOD 7] 
    ∨ 5^(2 * k) ≡ 4 [ZMOD 7] := by 
      convert h3 (5^(2 * k)) ⟨5^k, by ring⟩  using 1 <;> simp
    simp [hk, pow_add]
    rcases this with ht | ht | ht | ht 
    <;> replace ht := Int.ModEq.mul ht (show 5 ≡ 5 [ZMOD 7] by rfl)
    <;> simp at ht
    <;> try tauto
    have h5 (k : ℕ): ¬ 5 ^ k ≡ 0 [ZMOD 7] := by 
      intro hh 
      simp [Int.ModEq] at hh
      have : 7 ∣ 5 ^ k := by norm_cast at hh
      have := Nat.Prime.dvd_of_dvd_pow (show Nat.Prime 7 by norm_num) this
      omega
    exfalso
    exact h5 (2*k + 1) (by 
      rw [show (5 : ℤ) ^ (2 * k) * 5 = 5 ^ (2 * k + 1) by omega] at ht; assumption)  
  -- Or un carré est congru à $0,1,2$ ou 4 modulo 7 . 
  have h5 : 5^n ≡ 0 [ZMOD 7] ∨ 5^n ≡ 1 [ZMOD 7] ∨ 5^n ≡ 2 [ZMOD 7] ∨ 5^n ≡ 4 [ZMOD 7] := by 
    have := h3 (2 ^ n + 12 ^ n + 2014 ^ n ) isSq 
    simp at this 
    rcases this with ht | ht | ht | ht <;> replace ht := (ht.symm.trans h2).symm
    <;> tauto 
  -- Il n'existe donc pas d'entiers $n \geqslant 1$ tels que $2^{n}+12^{n}+2014^{n}$ soit un carré parfait.
  rcases h4 with h4 | h4 | h4 <;> rcases h5 with h5 | h5 | h5 | h5 
  <;> simp only [Int.ModEq] at h4 h5 <;> omega
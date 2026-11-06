import Mathlib

/-Let $n$ be an integer greater than 2. A positive integer is said to be attainable if it is 1 or can be obtained from 1 by a sequence of operations with the following properties: (i) The first operation is either addition or multiplication. (ii) Thereafter, additions and multiplications are used alternately. (iii) In each addition one can choose independently whether to add 2 or $n$. (iv) In each multiplication, one can choose independently whether to multiply by 2 or by $n$. A positive integer that cannot be so obtained is said to be unattainable. (a) Prove that if $n \geq 9$, there are infinitely many unattainable positive integers. -/
theorem Other_24851_a (n : ℕ) (hn : n > 2) (A M : Set ℕ)
  (hA : ∀ i ∈ A, i = 1 ∨ (∃ j ∈ M, i = j + 2 ∨ i = j + n))
  (hM : ∀ i ∈ M, i = 1 ∨ (∃ j ∈ A, i = j * 2 ∨ i = j * n))
  (hA' : 1 ∈ A ∧ (∀ i ∈ A, i * 2 ∈ M ∧ i * n ∈ M))
  (hM' : 1 ∈ M ∧ (∀ i ∈ M, i + 2 ∈ A ∧ i + n ∈ A)) :
  9 ≤ n → ∀ N, ∃ x, N ≤ x ∧ x ∉ A ∧ x ∉ M := by
    intro hn' N
    -- If $n$ is even, then every odd integer is unattainable. 
    by_cases hne : Even n
    · use (2 * N + n + 3)
      constructor
      linarith
      constructor
      · by_contra!
        specialize hA (2*N+n+3) this
        rcases hA with hA|hA
        · linarith
        · obtain ⟨k,hA1,hA2⟩ := hA
          specialize hM k hA1
          rcases hM with hM|hM
          · rcases hA2 with hA2|hA2 <;> omega
          have : Even k := by
            obtain ⟨t,ht,hM⟩ := hM
            rcases hM with hM |hM
            simp [hM]
            rw [hM]
            exact Even.mul_left hne t 
          have : Even (2 * N + n + 3) := by
            rcases hA2 with hA2 | hA2
            rw [hA2]
            refine Nat.even_add.mpr ?_
            simp [this]
            rw [hA2]
            refine Nat.even_add.mpr ?_
            simp [this,hne]
          apply Nat.even_add.mp at this
          have this' : Even (2 * N + n) := by
            refine Nat.even_add.mpr ?_
            simp [hne]
          simp [this'] at this
          have this' : ¬ Even 3 := by
            simp ;use 1 ;norm_num
          exact this' this
      · by_contra!
        specialize hM (2*N+n+3) this
        rcases hM with hM|hM
        · linarith
        · obtain ⟨k,hM1,hM2⟩ := hM
          have : Even (2 * N + n + 3) := by
            rcases hM2 with hM2|hM2 <;> rw [hM2] <;> simp [hne]
          have this' : ¬ Even (2 * N + n + 3) := by
            simp
            refine Nat.odd_add'.mpr ?_
            simp [show Odd 3 by use 1;simp]
            refine Nat.even_add.mpr ?_
            simp [hne]
          exact this' this
    -- Assume that $n \geq 9$ is odd.
    simp at hne
    -- Now consider any $a=k n(n-2)-2$, where $k$ is odd. If it is attainable, but not divisible by 2 or $n$, 
    use (2 * N + 3) * n * (n - 2) - 2
    constructor
    rw [mul_assoc,add_mul]
    have : 1 ≤ n - 2 := Nat.le_sub_of_add_le hn
    have :1 ≤ (n * (n - 2)) := by nlinarith
    refine Nat.le_sub_of_add_le ?_
    nlinarith
    -- Let $a$ be obtained by addition from some $b$, and $b$ from $c$ by multiplication. Then $a$ is $2 c+2,2 c+n, n c+2$, or $n c+n$, and is in every case congruent to $2 c+2$ modulo $n-2$. In particular, if $a \equiv-2$ $(\bmod n-2)$, then also $b \equiv-4$ and $c \equiv-2(\bmod n-2)$.
    have h1 : ∀ i ∈ A, (n - 2) ∣ i + 2 → ∃ j ∈ A, j ≤ i - 2 ∧ (n - 2) ∣ j + 2 := by
      intro i hi hdi
      specialize hA i hi
      rcases hA with hA|hA
      · simp [hA] at hdi
        apply Nat.le_of_dvd (by simp) at hdi
        omega
      rcases hA with ⟨j,hj,hA⟩
      specialize hM j hj
      rcases hM with hM|hM
      · rcases hA with hA|hA 
        simp [hA,hM] at hdi
        apply Nat.le_of_dvd (by simp) at hdi
        omega
        simp [hA,hM] at hdi
        apply dvd_iff_exists_eq_mul_left.mp at hdi
        obtain ⟨r,hr⟩ := hdi
        have hr1 : 1 < r := by
          by_contra! hnr
          have : 1 + n + 2 ≤ 1 * (n - 2) := by
            rw [hr]
            nlinarith
          ring_nf at this
          omega
        have hr2 : r < 2 := by
          by_contra! hnr
          have : 1 + n + 2 ≥ 2 * (n - 2) := by 
            rw [hr] ;nlinarith
          ring_nf at this
          omega
        interval_cases r
      obtain ⟨k,hk,hM⟩ := hM
      use k
      constructor
      exact hk
      constructor
      · rcases hA with hA|hA
        <;> rcases hM with hM|hM
        <;> rw [hA,hM]
        simp [Nat.le_mul_of_pos_right]
        simp
        apply Nat.le_mul_of_pos_right
        linarith
        rw [Nat.add_sub_assoc (by linarith)]
        refine Nat.le_add_right_of_le ?_
        apply Nat.le_mul_of_pos_right 
        simp
        rw [Nat.add_sub_assoc (by linarith)]
        refine Nat.le_add_right_of_le ?_
        apply Nat.le_mul_of_pos_right
        linarith
      have : n - 2 ∣ j + 4 := by
        rcases hA with hA|hA
        rw [hA,add_assoc] at hdi
        norm_num at hdi
        exact hdi
        have : i + 2 = j + 4 + (n - 2) := by
          rw [hA]
          zify [hn] ;ring_nf
        simp [this] at hdi
        exact hdi
      have hco2 : (n-2).Coprime 2 := by
        simp
        refine (Nat.odd_sub (by linarith)).mpr ?_
        simp [hne]
      rcases hM with hM|hM
      · rw [show j+4=2*(k+2) by rw [hM] ;ring_nf] at this
        apply (Nat.Coprime.dvd_mul_left hco2).mp at this
        exact this
      · have this' : j + 4 = (k + 2) * 2 + k * (n - 2) := by
          rw [hM] ;rify [hn] ;ring_nf
        rw [this'] at this
        apply (Nat.dvd_add_left (by simp)).mp at this
        apply (Nat.Coprime.dvd_mul_right hco2).mp at this
        exact this
    -- it must have been obtained by addition. Thus all predecessors of $a$ are congruent to either -2 or $-4(\bmod$ $n-2$ ), and none of them equals 1 , a contradiction. 
    have h2 (z : ℕ): ∀ i ∈ A, (n - 2) ∣ (i + 2) → ∃ j ∈ A, j ≤ i - 2 * z ∧ (n - 2) ∣ (j + 2) := by
      intros i hi hdi
      induction z with
      | zero =>
        use i ;simp [hi,hdi]
      | succ z ih =>
        obtain ⟨k,hk,hkz,hkd⟩ := ih
        specialize h1 k hk hkd
        obtain ⟨l,hl,hlk,hld⟩ := h1
        use l
        simp [hl,hld]
        omega
    constructor
    · by_contra! ha
      specialize h2 ((2 * N + 3) * n * (n - 2) - 2) ((2 * N + 3) * n * (n - 2) - 2) 
      rw [Nat.sub_add_cancel] at h2
      simp [ha] at h2
      obtain ⟨j,hj,hj1,_⟩ := h2 
      rw [two_mul ((2 * N + 3) * n * (n - 2) - 2), ← Nat.sub_sub] at hj1
      simp at hj1
      specialize hA j hj
      simp [hj1] at hA
      rcases hA with ⟨t,ht,ht1⟩
      linarith
      have hl1 : 2 ≤ 2 * N + 3 := by linarith
      have hl2 : 1 ≤ (n - 2) := Nat.le_sub_of_add_le hn
      have hl3 : 1 ≤ n * (n - 2) := by nlinarith
      rw [mul_assoc]
      nlinarith
    · by_contra! hm
      specialize hM ((2 * N + 3) * n * (n - 2) - 2) hm
      have hl1 : 3 ≤ 2 * N + 3 := by linarith
      have hl2 : 1 ≤ (n - 2) := Nat.le_sub_of_add_le hn
      have hl3 : 3 ≤ n * (n - 2) := by nlinarith
      rcases hM with hM|hM
      · replace hM : (2 * N + 3) * n * (n - 2) = 3 := by omega
        nlinarith
      · obtain ⟨k,hk,hk1⟩ := hM
        rcases hk1 with hk1|hk1
        have hk1' : 2 ∣ (2 * N + 3) * n * (n - 2) := by 
          have : (2 * N + 3) * n * (n - 2) = (2 * N + 3) * n * (n - 2) - 2 + 2 := by 
            rw [Nat.sub_add_cancel]
            nlinarith
          rw [this,hk1]
          simp
        rcases hne with ⟨p,hp⟩ 
        apply (Nat.Prime.dvd_mul (Nat.prime_two)).mp at hk1'
        rcases hk1' with hk1'|hk1'
        apply (Nat.Prime.dvd_mul (Nat.prime_two)).mp at hk1'
        rcases hk1' with hk1'|hk1'
        <;> simp [hp] at hk1'
        · have : 2 ∣ n := by
            rw [show n=n-2+2 by rw [Nat.sub_add_cancel] ;linarith]
            simp [hk1']
          simp [hp] at this
        have hk2 : n ∣ (2 * N + 3) * n * (n - 2) - 2 := by
          rw [hk1] ;simp
        have hk3 : n ∣ (2 * N + 3) * n * (n - 2) := by
          rw [mul_comm,← mul_assoc]
          simp
        have hk4 := Nat.dvd_sub' hk3 hk2
        rw [Nat.sub_sub_self (by nlinarith)] at hk4
        apply (Nat.le_iff_ne_zero_of_dvd (by linarith)) at hk4
        simp at hk4
        linarith


/-(b) Prove that if $n=3$, all positive integers except 7 are attainable.-/
theorem Other_24851_b (n : ℕ) (hn : n > 2) (A M : Set ℕ)
  (hA : ∀ i ∈ A, i = 1 ∨ (∃ j ∈ M, i = j + 2 ∨ i = j + n))
  (hM : ∀ i ∈ M, i = 1 ∨ (∃ j ∈ A, i = j * 2 ∨ i = j * n))
  (hA' : 1 ∈ A ∧ (∀ i ∈ A, i * 2 ∈ M ∧ i * n ∈ M))
  (hM' : 1 ∈ M ∧ (∀ i ∈ M, i + 2 ∈ A ∧ i + n ∈ A)) :
  n = 3 → (∀ x , x ≠ 7 ∧ x ≠ 0 → x ∈ A ∨ x ∈ M) ∧ (7 ∉ A ∧ 7 ∉ M) := by
    -- Call an attainable number addy if the last operation is addition, and multy if the last operation is multiplication.
    -- 也即我这里定义的A和M两个Set
    intro hn
    constructor
    intro x ⟨hx1,hx2⟩
    simp [hn] at hA hM hA' hM'
    rcases hA' with ⟨hA1,hA2⟩
    rcases hM' with ⟨hM1,hM2⟩
    -- We prove the following claims by simultaneous induction on $k$ : (1) $n=6 k$ is both addy and multy; (2) $n=6 k+1$ is addy for $k \geq 2$; (3) $n=6 k+2$ is addy for $k \geq 1$; (4) $n=6 k+3$ is addy; (5) $n=6 k+4$ is multy for $k \geq 1$; (6) $n=6 k+5$ is addy. 
    have h1 : ∀ m , ∀ k, k ≤ m → (((6*k+6)∈A)∧((6*k+6)∈M))∧ 
    (((6*k+7)∈A)∨(k=0))∧((6*k+8)∈A)∧((6*k+9)∈A)∧
    ((6*k+10)∈M)∧((6*k+11)∈A) := by
      intro m
      induction m with
      -- The cases $k \leq 1$ are easily verified. 
      | zero =>
        simp
        have h2 := hA2 1 hA1
        simp at h2
        have h3 := hM2 3 h2.2
        simp at h3
        have h4 := hM2 1 hM1
        simp at h4
        have h5 := hA2 3 h4.1
        simp at h5
        have h6 := hM2 6 h5.1
        simp at h6
        have h7 := hA2 5 h3.1
        simp at h7
        have h8 := hM2 9 h5.2
        simp at h8
        simp [h3.2,h5.1,h6.1,h6.2,h7.1,h8.1]
      -- For $k \geq 2$, suppose all six statements hold up to $k-1$. 
      | succ m ih =>
        intro k hmk
        by_cases hk : k≤m
        · apply ih
          exact hk
        push_neg at hk
        replace hk : k = m+1 := by linarith
        have h0 : 6 * k + 6 ∈ M := by
          let l := (3 * k + 3) / 6
          let u := (3 * k + 3) % 6
          have hu1 : 3 * k + 3 = 6 * l + u := Eq.symm (Nat.div_add_mod (3 * k + 3) 6)
          have hu2 : u = 3 ∨ u = 0 := by
            have : 3 ∣ u := by
              refine (Nat.dvd_mod_iff (by norm_num)).mpr (by simp)
            have this' : u < 6 := by
              refine Nat.mod_lt (3 * k + 3) (by simp)
            interval_cases u
            <;> omega
          by_cases hl1 : l = 0
          · rcases hu2 with hu2|hu2
            · have : k = 0 := by omega
              simp [this]
              specialize hM2 1 hM1
              simp at hM2
              specialize hA2 3 hM2.1
              simp at hA2
              exact hA2.1
            · omega
          replace hl1 : 1 ≤ l := by omega
          specialize ih (l-1) (by omega)
          have : 3 * k + 3 ∈ A := by
            rcases hu2 with hu2 | hu2
            · have : 3 * k + 3 = 6 * (l - 1) + 9 := by
                rw [hu1,hu2] ;rify [hl1] ;ring_nf
              rw [this]
              simp [ih]
            · have : 3 * k + 3 = 6 * (l - 1) + 6 := by
                rw [hu1,hu2] ;rify [hl1] ;ring_nf
              rw [this]
              simp [ih]
          specialize hA2 (3 * k + 3) this
          ring_nf at hA2
          ring_nf
          exact hA2.1
        constructor
        · constructor
          · -- Next, $6 k-2$ is multy, so both $6 k=(6 k-2)+2$ and $6 k+1=(6 k-2)+3$ are addy. 
            specialize ih m (by simp)
            specialize hM2 (6 * m + 10) ih.2.2.2.2.1
            rw [hk]
            ring_nf at hM2
            ring_nf
            exact hM2.1
          · -- Since $6 k-3$ is addy, $6 k$ is multy. 这里可能有些问题
            exact h0
        constructor
        · specialize ih m (by simp)
          specialize hM2 (6 * m + 10) ih.2.2.2.2.1
          rw [hk]
          ring_nf at hM2
          ring_nf
          simp [hM2.2]
        -- Since $6 k$ is multy, both $6 k+2$ and $6 k+3$ are addy.
        constructor
        · specialize hM2 (6 * k + 6) h0
          ring_nf at hM2
          ring_nf
          simp [hM2]
        constructor
        · specialize hM2 (6 * k + 6) h0
          ring_nf at hM2
          ring_nf
          simp [hM2]
        -- Number $6 k+4=2 \cdot(3 k+2)$ is multy, because $3 k+2$ is addy (being either $6 l+2$ or $6 l+5)$.
        constructor
        · have : 5 + 3 * k ∈ A := by
            have : Even k ∨ Odd k := by
              exact Nat.even_or_odd k
            rcases this with hk1|hk1
            · obtain ⟨d,hd⟩ := hk1
              specialize ih (d-1) (by omega)
              rw [hd]
              by_cases hd1 : 1 ≤ d
              · have : 6 * (d - 1) + 11 = 5 + 3 * (d + d) := by
                  rify [hd1] ;ring_nf
                rw [← this]
                simp [ih]
              push_neg at hd1
              have : d = 0 := by linarith
              simp [this]
              specialize hA2 1 hA1
              simp at hA2
              specialize hM2 2 hA2.1
              simp at hM2
              exact hM2.2
            · obtain ⟨d,hd⟩ := hk1
              specialize ih d (by omega)
              simp [hd]
              ring_nf
              ring_nf at ih
              simp [ih]
          specialize hA2 (5 + 3 * k) this
          ring_nf at hA2
          ring_nf
          exact hA2.1
        -- Finally, we have $6 k+5=3 \cdot(2 k+1)+2$. Since $2 k+1$ is $6 l+1,6 l+3$, or $6 l+5$, it is addy except for 7 . Hence $6 k+5$ is addy except possibly for 23 .
        let l := (2 * k + 3) / 6
        let u := (2 * k + 3) % 6
        have hu1 : 2 * k + 3 = 6 * l + u := by
          simp [l,u]
          exact Eq.symm (Nat.div_add_mod (2 * k + 3) 6)
        have hu2 : u ∈ [1,3,5] := by
          have hu3 : Odd u := by
            refine Odd.mod_even (by use (k+1) ;ring_nf) (by use 3)
          have hu4 : u < 6 := by
            refine Nat.mod_lt (2 * k + 3) (by simp)
          interval_cases u
          <;> simp
          <;> contrapose! hu3
          <;> simp
          use 2
        by_cases h1 : 2 * k + 3 ≠ 7
        have hk2 : (2 * k + 3) ∈ A := by
          by_cases hl : l = 0
          · simp [hu1,hl]
            simp at hu2
            rcases hu2 with hu2 |hu2 |hu2
            · simp [hu2,hA1]
            · specialize hM2 1 hM1
              simp at hM2
              simp [hu2,hM2]
            · specialize hA2 1 hA1
              simp at hA2
              specialize hM2 2 hA2.1
              simp at hM2
              simp [hu2,hM2]
          push_neg at hl
          replace hl : 1 ≤ l := by omega
          specialize ih (l-1) (by omega)
          simp [hu1]
          simp at hu2
          rcases hu2 with hu2 |hu2 |hu2
          · have : 6 * (l - 1) + 7 = 6 * l + u := by
              rify [hl] ;rw [hu2] ;ring_nf
            rw [← this]
            by_cases hl' : l - 1 ≠ 0
            · simp [hl'] at ih
              simp [ih]
            push_neg at hl'
            rw [hu1,hu2] at h1
            omega
          · have : 6 * (l - 1) + 9 = 6 * l + u := by
              rify [hl] ;rw [hu2] ;ring_nf
            rw [← this]
            simp [ih]
          · have : 6 * (l - 1) + 11 = 6 * l + u := by
              rify [hl] ;rw [hu2] ;ring_nf
            rw [← this]
            simp [ih]
        specialize hA2 (2*k+3) hk2
        ring_nf at hA2
        specialize hM2 (9+k*6) hA2.2
        ring_nf at hM2
        ring_nf
        exact hM2.1
        push_neg at h1
        -- But $23=((1 \cdot 2+2) \cdot 2+2) \cdot 2+3$ is also addy. This completes the induction. Now 1 is given and $2=1 \cdot 2,4=1+3$.
        replace h1 : k = 2 := by omega
        simp [h1]
        have h2 := hA2 1 hA1
        simp at h2
        have h3 := hM2 2 h2.1
        simp at h3
        have h4 := hA2 4 h3.1
        simp at h4
        have h5 := hM2 8 h4.1
        simp at h5
        have h6 := hA2 10 h5.1
        simp at h6
        have h7 := hM2 20 h6.1
        simp at h7
        exact h7.2
    by_cases h2 : x ≤ 7
    · have h3 := hA2 1 hA1
      simp at h3
      have h4 := hM2 2 h3.1
      simp at h4
      have h5 := hM2 3 h3.2
      simp at h5
      interval_cases x
      <;> simp at hx1 hx2
      <;> simp [h3,h4,h5,hA1]
    push_neg at h2
    let l := x / 6
    let u := x % 6
    have hu1 : x = 6 * l + u := Eq.symm (Nat.div_add_mod x 6)
    have hl1 : 1 ≤ l := by omega
    specialize h1 l (l-1) (by omega)
    have hu2 : u < 6 := by refine Nat.mod_lt x (by simp)
    interval_cases u
    · have : x = 6 * (l - 1) + 6 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      simp [this,h1]
    · have : x = 6 * (l - 1) + 7 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      have hl2 : l - 1 ≠ 0 := by omega
      simp [hl2] at h1
      simp [this,h1] 
    · have : x = 6 * (l - 1) + 8 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      simp [this,h1]
    · have : x = 6 * (l - 1) + 9 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      simp [this,h1]
    · have : x = 6 * (l - 1) + 10 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      simp [this,h1]
    · have : x = 6 * (l - 1) + 11 := by
        rw [hu1] ;rify [hl1] ;ring_nf
      simp [this,h1]
    -- It is easily checked that 7 is not attainable, and hence it is the only unattainable number.
    constructor
    · by_contra!
      have h1 := hA 7 this
      rcases h1 with h1|h1
      · linarith
      rcases h1 with ⟨j,hj1,hj2⟩
      rcases hj2 with hj2 |hj2
      · have hj3 : j = 5 := by omega
        specialize hM j hj1
        rw [hj3] at hM
        rcases hM with hM|hM
        · linarith
        rcases hM with ⟨k,hk1,hk2⟩
        rcases hk2 with hk2 | hk2
        omega
        have : 3 ∣ 5 := by simp [hk2,hn]
        omega
      have hj3 : j = 4 := by omega
      have hM' := hM j hj1
      rw [hj3] at hM'
      rcases hM' with hM'|hM'
      · linarith
      rcases hM' with ⟨k,hk1,hk2⟩
      rcases hk2 with hk2 | hk2
      · have hk3 : k = 2 := by omega
        have hA' := hA k hk1
        rw [hk3] at hA'
        rcases hA' with hA' | hA'
        · linarith
        rcases hA' with ⟨w,hw1,hw2⟩
        rcases hw2 with hw2 |hw2
        · have hw3 : w = 0 := by omega
          specialize hM w hw1
          rw [hw3] at hM
          simp [hn] at hM
          specialize hA 0 hM
          simp [hn] at hA
        linarith
      have : 3 ∣ 4 := by simp [hk2,hn]
      omega
    · by_contra!
      specialize hM 7 this
      rcases hM with hM|hM
      · linarith
      rcases hM with ⟨k,hk1,hk2⟩
      rcases hk2 with hk2 | hk2
      · omega
      have : 3 ∣ 7 := by simp [hk2,hn]
      omega




          
          


    


        


        
    
      


import Mathlib.Tactic

/- Show that we can link any two integers m, n greater than 2 by a chain of positive integers m = a 1 , a 2 , ... , a k+1 = n, so that the product of any two consecutive members of the chain is divisible by their sum. [For example, 7, 42, 21, 28, 70, 30, 6, 3 links 7 and 3.] -/
theorem number_theory_146978 (m n : ℤ) (hm : m > 2) (hn : n > 2) :
  ∃ k : ℕ, ∃ a : ℕ → ℤ,
    (∀ i ∈ Finset.range (k + 1), a i > 0) ∧
    a 0 = m ∧ a k = n ∧
    ∀ i ∈ Finset.range k, (a i) * (a (i + 1)) % (a i + a (i + 1)) = 0 := by
      -- We write a ↔ b if (a + b) divides ab.Here we use a Prop called G.
      let G : ℤ → ℤ → Prop := fun s t =>
        (∃ k : ℕ, ∃ a : ℕ → ℤ,
        (∀ i ∈ Finset.range (k + 1), a i > 0) ∧
        a 0 = s ∧ a k = t ∧
        ∀ i ∈ Finset.range k, (a i) * (a (i + 1)) % (a i + a (i + 1)) = 0)
      -- The starting point is that for n > 1 we have n ↔ n(n - 1).
      have h1 : ∀ p > 1, G p (p * (p - 1)):= by
        simp only [G]
        intro p hp
        use 1
        use fun i => if i = 0 then p else p * (p - 1)
        simp
        constructor
        intro i hi
        interval_cases i
        <;> simp <;> nlinarith
        nth_rewrite 1 [← mul_one p,← mul_add,add_comm,sub_add_cancel,← mul_assoc] ;simp
      -- As slight variants we also have 2n ↔ n(n - 2) for n > 2,
      have h2 : ∀ p > 2, G (2 * p) (p * (p - 2)):= by
        simp only [G]
        intro p hp
        use 1
        use fun i => if i = 0 then 2 * p else p * (p - 2)
        simp
        constructor
        intro i hi
        interval_cases i
        <;> simp <;> nlinarith
        rw [mul_comm,← mul_add,add_comm,sub_add_cancel,
        ← mul_assoc,mul_comm p 2,mul_assoc 2 p p,
        mul_comm 2,mul_assoc] ;simp
      --  and in any case where a ↔ b, then also ma ↔ mb (for m > 0).
      have h3 : ∀ a b, G a b → (∀ m > 0, G (m * a) (m * b)) := by
        simp only [G]
        intro a b hab m hm
        rcases hab with ⟨k, t, ht, ⟨ht0, htk ,htdvd⟩⟩
        use k
        use (fun i => m * t i)
        simp [ht0,htk]
        constructor
        intro i hi
        simp at ht
        apply ht at hi
        nlinarith
        intro i hi
        simp at htdvd
        apply htdvd at hi
        rw [← mul_add,mul_assoc]
        refine Int.mul_dvd_mul_left m ?_
        rw [mul_comm,mul_assoc,mul_comm (t (i + 1))]
        exact Dvd.dvd.mul_left hi m
      -- G is transitive.
      have h4 : ∀ a b c, G a b ∧ G b c → G a c := by
        simp only [G]
        intro a b c ⟨⟨k1,t1,ht1,ht10,ht1k1,ht1dvd⟩,⟨k2,t2,ht2,ht20,ht2k2,ht2dvd⟩⟩
        use (k1 + k2)
        use fun i => if i < k1 then t1 i else t2 (i - k1)
        simp [ht10,ht20,ht1k1,ht2k2]
        constructor
        · intro i hi
          by_cases him : i < k1
          · simp [him] ;apply ht1 ;simp ;linarith
          · simp [him] ;apply ht2 ;simp ;omega
        constructor
        · intro hk1 ;rw [← ht10, ← ht1k1, hk1]
        · intro i hi
          by_cases hi1 : i + 1 < k1
          · have : i < k1 := by linarith
            simp [hi1,this]
            simp at ht1dvd
            apply ht1dvd
            exact this
          by_cases hi2 : i < k1
          · have : i + 1 = k1 := by omega
            simp [hi1,hi2]
            rw [this,Nat.sub_self,ht20,← ht1k1,← this]
            simp at ht1dvd
            apply ht1dvd ;exact hi2
          · simp [hi1,hi2]
            have : i + 1 - k1 = i - k1 + 1 := by omega
            rw [this]
            simp at ht2dvd
            apply ht2dvd ;omega
      -- G is symmetric.
      have h5 : ∀ a b, G a b → G b a := by
        simp only [G]
        intro a b ⟨k,t,⟨ht,ht0,htk,htdvd⟩⟩
        use k
        use fun i => t (k - i)
        simp [ht0,htk]
        constructor
        · intro i hi
          apply ht
          simp ;omega
        · intro i hi
          have : k - i = k - (i + 1) + 1 := by omega
          rw [add_comm,mul_comm,this]
          simp at htdvd
          apply htdvd ;omega
      -- we need use h6_1 to prove h6.
      have h6_1 : ∀ p > 2, G (p*(p-1)) (p*(p-1)*(p-2)) := by
        intro p hp
        simp only [G]
        use 1
        use fun i => if i = 0 then p * (p - 1) else p * (p - 1) * (p - 2)
        simp
        constructor
        intro i hi
        interval_cases i
        <;> simp
        nlinarith
        refine Int.mul_pos (by nlinarith) (by nlinarith)
        nth_rewrite 1 [← mul_one (p * (p - 1)),← mul_add]
        have : 1 + (p - 2) = p - 1 := by omega
        rw [this]
        nth_rewrite 3 [mul_comm p (p-1)]
        rw [← mul_assoc,← mul_assoc]
        nth_rewrite 2 [mul_assoc] ;simp
      -- That allows us to link n > 2 and 2n, thus: n ↔ n(n - 1) ↔ n(n - 1)(n - 2) = n(n - 2) ↔ 2n.
      have h6 : ∀ p > 2, G p (2 * p) := by
        intro p hp
        have h6_2 : G (p*(p-1)*(p-2)) (p*(p-2)) := by
          simp only [G]
          use 1
          use fun i => if i = 0 then p * (p - 1) * (p - 2) else p * (p - 2)
          simp
          constructor
          intro i hi
          interval_cases i
          <;> simp
          refine Int.mul_pos (by nlinarith) (by nlinarith)
          nlinarith
          nth_rewrite 1 [← mul_one (p * (p - 2)), mul_assoc, mul_comm (p - 1), ← mul_assoc,
          ← mul_add,sub_add_cancel, mul_comm (p * (p - 1) * (p - 2)), ← mul_assoc, ← mul_assoc,
          mul_assoc (p * (p - 2) * p)] ;simp
        specialize h1 p (by linarith)
        specialize h2 p hp
        specialize h6_1 p hp
        apply h5 at h2
        apply h4 p (p * (p - 1)) ;simp [h1]
        apply h4 (p * (p - 1)) (p * (p - 1) * (p - 2)) ;simp [h6_1]
        apply h4 (p * (p - 1) * (p - 2)) (p * (p - 2)) ;simp [h6_2,h2]
      -- To go much further we need some inspiration. Note that n(n - 3) + 2 = (n - 1)(n - 2). So 2(n - 1)(n - 2) ↔ n(n - 3)(n - 1)(n - 2).
      have h7 : ∀ p > 3, G (2 * (p - 1) * (p - 2)) (p * (p - 1) * (p - 2) * (p - 3)) := by
        simp only [G]
        intro p hp
        use 1
        use fun i => if i = 0 then (2 * (p - 1) * (p - 2)) else (p * (p - 1) * (p - 2) * (p - 3))
        simp
        constructor
        intro i hi
        interval_cases i
        <;> simp ;nlinarith ;refine Int.mul_pos ?_ (by nlinarith) ;refine Int.mul_pos (by nlinarith) (by nlinarith)
        have h7_1 : 2 * (p - 1) * (p - 2) + p * (p - 1) * (p - 2) * (p - 3)  = (p - 1) ^ 2 * (p - 2) ^ 2 := by ring_nf
        have h7_2 : 2 * (p - 1) * (p - 2) * (p * (p - 1) * (p - 2) * (p - 3)) = (p - 1) ^ 2 * (p - 2) ^ 2 * (2 * p * (p - 3)) := by ring_nf
        rw [h7_1, h7_2] ;simp
      -- That is critical, for it is a general way of allowing us to reduce the largest factor.
      -- Thus for n > 3, n ↔ n(n - 1) ↔ n(n - 1)(n - 2) ↔ n(n - 1)(n - 2)(n - 3) ↔ 2(n - 1)(n - 2) ↔ (n - 1)(n - 2) ↔ n - 1.
      have h8 : ∀ p > 3, G p (p - 1) := by
        intro p hp
        have := h1 p (by linarith)
        specialize h6_1 p (by linarith)
        have h7_1 : G (p * (p - 1) * (p - 2)) (p * (p - 1) * (p - 2) * (p - 3)) := by
          simp only [G]
          use 1
          use fun i => if i = 0 then p * (p - 1) * (p - 2) else p * (p - 1) * (p - 2) * (p - 3)
          simp
          constructor
          intro i hi
          interval_cases i
          <;> simp
          refine Int.mul_pos (by nlinarith) (by nlinarith)
          refine Int.mul_pos ?_ (by nlinarith)
          refine Int.mul_pos (by nlinarith) (by nlinarith)
          have : p * (p - 1) * (p - 2) + p * (p - 1) * (p - 2) * (p - 3) = p * (p - 1) * (p - 2) ^ 2 := by ring_nf
          have this' : p * (p - 1) * (p - 2) * (p * (p - 1) * (p - 2) * (p - 3)) = p  * (p - 1) * (p - 2) ^ 2 * (p * (p - 1) * (p - 3)) := by ring_nf
          rw [this, this'] ;simp
        specialize h7 p hp
        apply h5 at h7
        have h7_2 : 2 < ((p - 1) * (p - 2)) := by
          have : 2 < p - 1 := by linarith
          have : 1 < p - 2 := by linarith
          nlinarith
        specialize h6 ((p - 1) * (p - 2)) h7_2
        apply h5 at h6
        specialize h1 (p - 1) (by linarith)
        apply h5 at h1
        have h1' : p - 1 - 1 = p - 2 := by omega
        rw [h1'] at h1
        apply h4 p (p * (p - 1)) ;simp [this]
        apply h4 (p * (p - 1)) (p * (p - 1) * (p - 2)) ;simp [h6_1]
        apply h4 (p * (p - 1) * (p - 2)) (p * (p - 1) * (p - 2) * (p - 3)) ;simp [h7_1]
        apply h4 (p * (p - 1) * (p - 2) * (p - 3)) (2 * (p - 1) * (p - 2)) ;simp [h7]
        apply h4 (2 * (p - 1) * (p - 2)) ((p - 1) * (p - 2)) ;rw [mul_assoc] ;simp [h6,h1]
      -- G is self-reflexive.
      have h9 : ∀ p > 0, G p p := by
        simp only [G]
        intro p hp
        use 0
        use fun i => p
        simp [hp]
      -- But linking n and n-1 obviously allows us to link any two integers > 3.
      have h10 : ∀ p (x : ℕ), 3 < p → G p (p + x) := by
        intro p x hp
        induction x with
        | zero => simp ;apply h9 ;linarith
        | succ x ih =>
          specialize h8 (p + ↑(x + 1)) (by linarith)
          have : (p + ↑(x + 1) - 1) = (p + ↑x) := by omega
          rw [this] at h8 ;apply h5 at h8 ;simp at h8
          apply h4 p (p + ↑x) ;simp [ih, h8]
      -- That leaves 3 itself, but the question already shows how to link that to at least one integer > 3, which is all we need.
      have h11 : ∀ p > 3, G 3 p := by
        intro p hp
        have h11_1 : G 7 3 := by
          simp only [G]
          use 7
          use fun i => if i = 0 then 7 else
            if i = 1 then 42 else
            if i = 2 then 21 else
            if i = 3 then 28 else
            if i = 4 then 70 else
            if i = 5 then 30 else
            if i = 6 then 6 else 3
          simp
          constructor
          intro i hi
          interval_cases i
          <;> simp
          intro i hi
          interval_cases i
          <;> simp
          <;> norm_num
        have h11_2 : G p 3 := by
          by_cases hp' : p < 7
          · specialize h10 p (7 - p).natAbs hp
            have : p + ↑(7 - p).natAbs = 7 := by omega
            rw [this] at h10
            apply h4 p 7 ;simp [h10, h11_1]
          by_cases hp'' : 7 < p
          · specialize h10 7 (p - 7).natAbs (by simp)
            have : 7 + ↑(p - 7).natAbs = p := by omega
            rw [this] at h10 ;apply h5 at h10
            apply h4 p 7 ;simp [h10, h11_1]
          have : p = 7 := by omega
          rw [this] ;exact h11_1
        apply h4 3 p
        constructor ;apply h5 ;exact h11_2 ;apply h9 ;linarith
      -- Now we can prove the main result.
      have h12 : G m n := by
        by_cases hm : 3 < m
        · by_cases hn : m < n
          · specialize h10 m (n - m).natAbs hm
            have : m + ↑(n - m).natAbs = n := by omega
            rw [this] at h10 ;apply h5 at h10
            apply h5 ;exact h10
          by_cases hn' : 3 < n
          · specialize h10 n (m - n).natAbs hn'
            have : n + ↑(m - n).natAbs = m := by omega
            rw [this] at h10 ;apply h5 at h10
            exact h10
          · have hn : n = 3 := by omega
            rw [hn] ;apply h5 ;apply h11 ;exact hm
        · have hm : m = 3 := by omega
          rw [hm]
          by_cases hn : 3 < n
          · apply h11 ;linarith
          · have hn : n = 3 := by omega
            rw [hn] ;apply h9 ;simp
      simp only [G] at h12
      exact h12


        


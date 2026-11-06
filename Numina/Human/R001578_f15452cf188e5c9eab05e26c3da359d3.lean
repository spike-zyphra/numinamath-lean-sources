
import Mathlib

/- 19. N1 (UKR) Four integers are marked on a circle. At each step we simultaneously replace each number by the difference between this number and the next number on the circle, in a given direction (that is, the numbers $a, b, c, d$ are replaced by $a-b, b-c, c-d, d-a)$. Is it possible after 1996 such steps to have numbers $a, b, c, d$ such that the numbers $|b c-a d|,|a c-b d|,|a b-c d|$ are primes? -/
theorem number_theory_24687 
    (replace : (Fin 4 → ℤ) → (Fin 4 → ℤ))
    (h_replace : ∀ f i, replace f i = f i - f ((i + 1))) :
    ¬∃ start : (Fin 4 → ℤ), ∃ a b c d,
    ![a,b,c,d] = replace^[1996] start 
    ∧  
    Nat.Prime ((b * c - a * d : ℤ).natAbs) ∧ Nat.Prime ((a * c - b * d : ℤ).natAbs) ∧ Nat.Prime ((a * b - c * d : ℤ).natAbs):= by
  -- After one step we have $a+b+c+d=0$. 
  by_contra h
  rcases h with ⟨start, a, b, c, d, habcd, h₂, h₃, h₄⟩
  set before_end := replace^[1995] start with h_before_end
  have : replace^[1996] start = replace (replace^[1995] start) := by 
    rw [Function.iterate_succ']
    simp only [Function.comp_apply]
  rw [this] at habcd
  clear this
  clear_value before_end
  rw [<-h_before_end] at habcd
  clear h_before_end
  have sum_eq_zero : a + b + c + d = 0 := by  
    have : ∃ a' b' c' d', ![a',b',c',d'] = before_end := by
      use before_end 0, before_end 1, before_end 2, before_end 3
      ext i
      fin_cases i <;> rfl
    obtain ⟨a', b', c', d', habcd'⟩ := this
    rw [<-habcd'] at habcd
    have ha : a = replace ![a', b', c', d'] 0 := by
      rw [<-habcd]
      simp
    have hb : b = replace ![a', b', c', d'] 1 := by
      rw [<-habcd]
      simp
    have hc : c = replace ![a', b', c', d'] 2 := by
      rw [<-habcd]
      simp
    have hd : d = replace ![a', b', c', d'] 3 := by
      rw [<-habcd]
      simp
    simp [h_replace] at ha hb hc hd
    simp [ha, hb, hc, hd]
  clear habcd before_end h_replace replace start
  -- Then $a c-b d=$ $a c+b(a+b+c)=(a+b)(b+c)$ etc., so $$ |a b-c d| \cdot|a c-b d| \cdot|a d-b c|=(a+b)^{2}(a+c)^{2}(b+c)^{2} $$ 
  have prod_abs : 
      ((b * c - a * d : ℤ).natAbs) * (a * c - b * d : ℤ).natAbs * (a * b - c * d : ℤ).natAbs 
      = (((a + b) * (a + c) * (b + c)).natAbs)^2:= by
    clear h₂ h₃ h₄
    have h1 : d = - (a + b + c) := by linarith
    have eq1 : b * c - a * d = (a + b) * (a + c) := by
      rw [h1]
      ring
    have eq2 : a * c - b * d = (a + b) * (b + c) := by
      rw [h1]
      ring
    have eq3 : a * b - c * d = (a + c) * (b + c) := by
      rw [h1]
      ring
    rw [eq1, eq2, eq3]
    have eq5 : ((a + b) * (a + c)).natAbs * ((a + b) * (b + c)).natAbs * ((a + c) * (b + c)).natAbs =
        ((a + b) * (a + c) * (b + c)).natAbs ^ 2 := by
      have h2 : ((a + b) * (a + c)).natAbs * ((a + b) * (b + c)).natAbs * ((a + c) * (b + c)).natAbs =
          (((a + b) * (a + c) * (a + b) * (b + c) * (a + c) * (b + c))).natAbs := by
        simp [Int.natAbs_mul]
        <;> ring_nf <;> omega
      rw [h2]
      have h3 : ((a + b) * (a + c) * (a + b) * (b + c) * (a + c) * (b + c) : ℤ) =
          (( (a + b) * (a + c) * (b + c) ) ^ 2 ) := by
        ring
      rw [h3]
      simp [Int.natAbs_pow]
      <;> ring_nf <;> omega
    simpa using eq5
  -- However, the product of three primes cannot be a square, 
  have product_three_primes_not_square (x y z n : ℕ) 
      (xp : x.Prime) (yp : y.Prime) (zp : z.Prime) (h : x * y * z = n^2) : False := by
    -- In fact, if a product of a multiset of primes is a perfect kth power, 
    -- then the cardinality of the multiset is a multiple of k
    have multiset_prime_product_eq_pow (s : Multiset ℕ) ( k : ℕ) (hk : 0 < k) (h : (∀ n ∈ s, Nat.Prime n))
    (h1 : ∃ m, s.prod = m ^ k) :
    k ∣ s.card := by 
      obtain ⟨m, hm⟩ := h1
      have prod_nonzero : s.prod ≠ 0 := by 
        simp
        by_contra h0

        have := h 0 h0
        norm_num at this
      have : s.card = ArithmeticFunction.cardFactors s.prod := by 
        rw [ArithmeticFunction.cardFactors_multiset_prod prod_nonzero]
        have : Multiset.map (⇑ArithmeticFunction.cardFactors) s = Multiset.map (fun _ => 1) s := by 
          refine Multiset.map_congr rfl ?_
          intro x hx
          simp
          exact h x hx
        rw [this]
        simp
      rw [this, hm]
      clear this
      have ArithmeticFunction.cardFactors_pow (m k) : ArithmeticFunction.cardFactors (m ^ k) = k * ArithmeticFunction.cardFactors m := by 
        by_cases hm : m ≠ 0
        · 
          induction k with
          | zero => simp
          | succ n ih => 
            simp [pow_succ]
            rw [ArithmeticFunction.cardFactors_mul, ih]
            ring
            exact pow_ne_zero n hm
            exact hm
        push_neg at hm
        subst hm
        cases k <;> simp
        done
      rw [ArithmeticFunction.cardFactors_pow]
      simp      
    have : 2 ∣ Multiset.card {x,y,z} := by
      apply multiset_prime_product_eq_pow {x, y, z} 2 (by decide)
      · simp [xp,yp,zp]
      · use n
        simp [<- h]
        ring
    simp at this
    contrapose this
    simp
  -- hence the answer is $n o$.  
  apply product_three_primes_not_square _ _ _ _ h₂ h₃ h₄ prod_abs
  

  

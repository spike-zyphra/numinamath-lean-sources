import Mathlib

/-
Represent $2012$ as the sum of $n$ consecutive natural numbers ($n\geqslant 2$), then $n$ has (   ) different values.

A:$0$

B:$1$

C:$2$

D:$3$
-/

theorem number_theory_628053 : {n : ℕ | ∃ k : ℕ, n ≥ 2 ∧ ∑ i ∈ Finset.range n, (k + i) = 2012}.ncard = 1 := by 

  --Sume of the consecutive integers.
  have clasum : ∀ n, ∀ a, ∑ i ∈ Finset.range n, (a+i) = (2*a+n-1)*n/2  := by
    
    have tmp : ∀ n:ℕ, ∀ a:ℕ, ∑ i ∈ Finset.range n, ((a:ℝ)+i) = (2*a+n-1)*n/2  := by
    
      intro n
      induction' n with n hn

      simp

      intro a
      rw [Finset.sum_range_succ]
      specialize hn a
      rw [hn]
      field_simp
      ring
    
    intro n a
    rify
    rw [tmp]
    by_cases ne0 : n = 0
    simp [ne0]
    have nge1: 1 ≤ n := by omega
    have t1: @Nat.cast ℤ AddMonoidWithOne.toNatCast (2 * a + n - 1) = 2*a+n-1 := by omega
    rw [t1]
    field_simp
    have :@HDiv.hDiv ℤ ℤ ℤ instHDiv ((2 * ↑a + ↑n - 1) * ↑n) 2= (2*(a:ℝ)+(n:ℝ)-1) * n/2 := by
      field_simp
      norm_cast
      refine Int.ediv_two_mul_two_of_even ?_
      by_cases evenn : Even n
      simp [evenn]
      have oddn: Odd n := by exact Nat.not_even_iff_odd.mp evenn
      have : Even (Int.subNatNat (2 * a + n) 1) := by 
        have h1: Odd ((2 * a + n)) := by 
          have : Even (2*a) := by use a; omega
          exact Even.add_odd this oddn
        have h2: Odd 1 := by decide
        obtain ⟨k,hk⟩ := h1
        obtain ⟨l,hl⟩ := h2
        use (k-l)
        ring_nf
        have : (k:ℤ) * 2  - ↑l * 2 = ((k:ℤ) * 2 +1)  - (↑l * 2 +1) := by omega
        rw [this]
        zify at hk hl
        nth_rw 2 [mul_comm]
        nth_rw 3 [mul_comm]
        rw [←hk]
        rw [←hl]
        norm_cast
        rw [mul_comm]

      exact Even.mul_right this ↑n
    rw [this]
    ring


    
    
  --Now we prove that n has to be 8.
  have cla : {n : ℕ | ∃ k : ℕ, n ≥ 2 ∧ ∑ i ∈ Finset.range n, (k + i) = 2012} = {8} := by 
    ext n
    simp

    constructor
    intro ⟨nge2, h⟩
    obtain ⟨a,h⟩ := h
    have t1 : ∑ i ∈ Finset.range n, (a + i) = (2*a+n-1)*n/2 := by apply clasum
    rw [t1]at h
    ring_nf at h
    --Use our formula, we have n ∣ 4024.
    have eq : n * (a * 2 + n - 1) = 4024 := by 
      have : 4024 = n * (a * 2 + n - 1) / 2 * 2 := by rw [h]; norm_num
      rw [this]
      refine Eq.symm (Nat.div_two_mul_two_of_even ?_)
      by_cases evenn : Even n 
      exact Even.mul_right evenn (a * 2 + n - 1)
      have oddn : Odd n := by exact Nat.not_even_iff_odd.mp evenn
      have s1: Even (n-1) := by refine Odd.tsub_odd oddn ?_; use 0; norm_num
      have s2: Even (a*2) := by use a; ring
      have : (a * 2 + n - 1) = (a*2+(n-1)) := by omega
      rw [this]
      refine Nat.even_mul.mpr ?_
      right
      exact Even.add s2 s1
    --Hence, n ∈ {1,2,4,8,503,1006,2012,4024}, the divisors of 4024.
    have di4024 : Nat.divisors 4024 = {1,2,4,8,503,1006,2012,4024} := by native_decide
    have : n ∣ 4024 := by use (a*2+n-1); symm; exact eq
    have : n ∈ Nat.divisors 4024 := by simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]; exact this
    rw [di4024] at this
    simp at this
    --We simply enumerate every case and check.
    rcases this with ne | ne | ne | ne | ne | ne | ne | ne <;>
    simp [ne] at h eq <;> omega

    --n = 8 is valid by considering the numbers starting from 248.
    intro ne
    simp [ne]
    use 248
    norm_num

  rw [cla]
  simp
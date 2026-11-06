import Mathlib

/-Each of the positive integers $a, b$, and $c$ has three digits, and for each of these integers the first digit is the same as its last digit. Also $b=2 a+1$ and $c=2 b+1$. How many possibilities are there for the integer $a$ ?
A 0
B 1
C 2
D 3
E more than 3-/
theorem number_theory_239133 : {a :ℕ | ∃ b c : ℕ , (∀ i ∈ [a,b,c], ∃ m n,(m > 0 ∧ m < 10 ∧ n < 10 ∧ i = m + 10 * n + 100 * m)) ∧ (b = 2 * a + 1) ∧ (c = 2 * b + 1)} = {181,191} := by
  apply Set.ext
  simp
  intro a
  constructor
  intro ⟨ha,hb,hc⟩
  -- Let the digits of $a$ be 'pqp', so $a=101 p+10 q$.
  obtain ⟨p,ha11,ha12,⟨q,ha2,ha⟩⟩ := ha
  obtain ⟨b1,hb11,hb12,⟨b2,hb2,hab⟩⟩ := hb
  obtain ⟨c1,hc11,hc12,⟨c2,hc2,hac⟩⟩ := hc
  -- Also $c=2 b+1=2(2 a+1)+1=4 a+3$ which is $404 p+40 q+3$. This is less than 1000 , so $p=1$ or 2 
  have hp : p ≤ 2 := by
    ring_nf at hac
    have : 3 + a * 4 < 1000 := by nlinarith
    rw [ha] at this
    ring_nf at this
    nlinarith
  -- If $p=2$, then $c=808+40 q+3$. This ends with digit $1(8+3=11)$ but $c$ is a 3-digit number greater than 808 so can't begin with 1 .
  by_cases hp' :p = 2
  · simp [ha,hp'] at hac
    ring_nf at hac
    have : c1 = (811 + q * 40) % 10 := by
      omega
    rw [show 40 = 4*10 by norm_num,← mul_assoc,Nat.add_mod] at this 
    norm_num at this
    omega
  -- If $p=1$, then $c=404+40 q+3$. This ends with digit $4+3=7$, so must also begin with 7 , 
  interval_cases p
  simp [ha] at hac 
  ring_nf at hac
  have : c1 = (407 + q * 40) % 10 := by
    omega
  rw [show 40 = 4*10 by norm_num,← mul_assoc,Nat.add_mod] at this 
  norm_num at this
  -- hence $700 \leq 404+40 q+3 < 800$ and thus $293 \leq 40 q < 393$. Therefore $q=8$ or 9 . 
  have hq : 8 ≤ q ∧ q ≤ 9 := by
    by_contra! hq
    by_cases h : q < 8
    · nlinarith
    simp at h
    simp [h] at hq
    nlinarith
  rcases hq with ⟨hq1,hq2⟩
  interval_cases q
  -- When $q=8$, this gives $a=181, b=363, c=727$. When $q=9$, this gives $a=191, b=383$, $c=767$. Hence there are two possibilities for $a, 181$ and 191 .
  rw [ha] ;norm_num
  rw [ha] ;norm_num
  simp at hp'
  intro ha
  rcases ha with ha|ha
  constructor
  · use 1 ;simp ;use 8 ;simp [ha]
  constructor
  · use 3 ;simp ;use 6 ;simp [ha]
  · use 7 ;simp ;use 2 ;simp [ha]
  constructor
  · use 1 ;simp ;use 9 ;simp [ha]
  constructor
  · use 3 ;simp ;use 8 ;simp [ha]
  · use 7 ;simp ;use 6 ;simp [ha]
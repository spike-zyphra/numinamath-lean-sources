import Mathlib

/-
Several numbers are written on the board. In one move, it is allowed to take any two of them $a$ and $b$, both not equal to zero, and replace them with the numbers $a-b / 2$ and $b+\frac{a}{2}$. Can the original numbers be obtained on the board after several such moves?

#
-/

theorem algebra_213908 (S : ℕ → Multiset ℝ) (h: ∀ n:ℕ, ∃a ∈ (S n), ∃b ∈ (S n), a ≠ 0 ∧ b ≠ 0 ∧ (a=b → 2 ≤ (Multiset.count a (S n))) ∧ (S (n+1) = ((S n) - {a,b})+ {a-b/2, b+a/2})) :
∀n>0, (S n) ≠ (S 0) := by 
  
  let g : ℝ → ℝ  := fun x => x^2
  let T : ℕ → Multiset ℝ  := fun n => (Multiset.map g (S n))
  let f : ℕ → ℝ  := fun n => (T n).sum


  --We will prove that after each operation, the sum of squares of these numbers strictly increases.
  have cla : StrictMono f := by 
    have tmp : ∀n:ℕ, f n < f (n+1) := by
      intro n
      specialize h n
      obtain ⟨a, ainSn, b, binSn, ane0, bne0, heq, h⟩ := h

      have : f (n+1) - f (n) = (a-b/2)^2 + (b+a/2)^2 - a^2 - b^2 := by 
        simp [f,T,g,h]
        have : (Multiset.map (fun x => x ^ 2) (S n)).sum = (Multiset.map (fun x => x ^ 2) (((S n).erase a).erase b)).sum + b^2 + a^2 := by 
          have : S n = ((S n).erase a).erase b + ({a,b}:Multiset ℝ) := by
            simp
            have t1: b ::ₘ ((S n).erase a).erase b = ((S n).erase a) := by
              have : b ∈ ((S n).erase a) := by 
                by_cases aeb : a = b
                have mula : 2 ≤ Multiset.count a (S n) := by
                  apply heq
                  exact aeb
                rw [←aeb]
                have : Multiset.count a ((S n).erase a) = (Multiset.count a (S n)) - 1 := by
                  simp
                have : 1 ≤ Multiset.count a ((S n).erase a) := by 
                  rw [this]
                  omega
                exact Multiset.count_pos.mp this

                rw [Multiset.mem_erase_of_ne]
                exact binSn
                symm
                push_neg at aeb
                exact aeb

                
              simp [this]
            have t2: (((S n).erase a).erase b + {b}) = b ::ₘ ((S n).erase a).erase b := by 
              rw [add_comm]
              simp
            rw [t2,t1]
            simp [ainSn]
          nth_rw 1 [this]
          simp
          ring
        rw [this]
        ring

      have : 0 < (a-b/2)^2 + (b+a/2)^2 - a^2 - b^2 := by 
        ring_nf
        positivity
      linarith
      
    apply strictMono_of_lt_succ
    simp
    exact tmp

  have cor : Function.Injective f := by exact StrictMono.injective cla

  --Since the sum of the squares increases, this shows that we can never get the original set of numbers.
  by_contra exi
  push_neg at exi
  obtain ⟨n, npos, eq⟩ := exi
  have : T n = T 0 := by 
    simp [T]
    rw [eq]
  have : f n = f 0 := by 
    simp [f]
    rw [this]
  apply cor at this
  linarith
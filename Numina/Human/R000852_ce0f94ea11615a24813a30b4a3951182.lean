import Mathlib

/-
What is the sum of all the odd integers between $500$ and $700$?-/

theorem algebra_18605 : ∑ n in (Finset.Ioo 500 700).filter Odd, n = 60000 := by
    --We want to find the sum of the arithmetic series $501 + 503 + \dots + 699$.
    --The common difference is 2, so the $n^{\text{th}}$ term in this arithmetic sequence is $501 + 2(n - 1) = 2n + 499$.  If $2n + 499 = 699$, then $n = 100$, so the number of terms in this sequence is 100.
    --The sum of an arithmetic series is equal to the average of the first and last term, multiplied by the number of terms, so the sum is $(501 + 699)/2 \cdot 100 = \boxed{60000}$.
    have h :  (Finset.Ioo 500 700).filter Odd =  Finset.image (fun (n) => ((n + 1) * 2 + 499)) (Finset.range 100) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ioo, Finset.mem_range,Finset.mem_Ico]
      constructor
      .
        intro h
        rcases  h with ⟨hx1, hx2⟩ 
        use ((x - 499) / 2 ) - 1
        have h3 : 0 <  (x - 499)  := by omega
        have ho : Odd 499 := by  
         rw [Odd]
         use 249
         ring_nf
        have h3 : Even (x - (499)) := by
          apply Nat.Odd.sub_odd hx2 ho
        --zify at [h3]
        have hd : 2 ∣  (x -499 )  := by
           apply Even.two_dvd h3
        
        constructor
        .
          omega
        .
          ring_nf
          omega
      .
        intro h
        constructor
        .
          omega
        .
          rcases  h with ⟨a, ha⟩ 
          aesop
          rw [Odd]
          simp
          use a+250
          ring_nf
    simp_rw [h]
    apply Finset.sum_image
    simp

    

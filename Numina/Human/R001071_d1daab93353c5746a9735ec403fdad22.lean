import Mathlib

/-Simplify $\frac{1+\sqrt{2}}{2+\sqrt{3}}$. Your solution can be converted to the form $A(1+\sqrt{B})-(\sqrt{C}+\sqrt{D})$, where $A$, $B$, $C$, and $D$ are positive integers. What is $A+B+C+D$?-/

theorem algebra_20303 {A B C D : ℤ} (hA : A > 0) (hB : B > 0) (hC : C > 0) (hD : D > 0)

    (h : (1 + Real.sqrt 2) / (2 + Real.sqrt 3) = 2 - √3 + 2 * √2 - √6 →  A = 2 ∧ B = 3 ∧ C = 2 ∧ D = 6) :

    A + B + C + D = 13 := by
    --Multiplying top and bottom by the conjugate, we have $\frac{1+\sqrt{2}}{2+\sqrt{3}} = \frac{(1+\sqrt{2})(2-\sqrt{3})}{(2+\sqrt{3})((2-\sqrt{3}))} = \frac{2-\sqrt{3}+2\sqrt{2}-\sqrt{6}}{4-3} = 2-\sqrt{3}+2\sqrt{2}-\sqrt{6}$. So, we obtain $A=2, B=2, C=3$ and $D=6$ ($C$ and $D$ are interchangeable). So $A+B+C+D = 2+2+3+6 = \boxed{13}$.
    have heq : (1 + √2) / (2 + √3) = 2 - √3 + 2 * √2 - √6 := by
      have heq2 : (1 + √2) / (2 + √3) = (1 + √2) / (2 + √3) * ((2 - √3) / (2 - √3)) := by
        have hgez :  0 < (2 - √3) := by
          have hge2 :  √3 < 2 := by
            have  hge3  : √3 *√3  < 2 * 2 := by
              simp; ring_nf;
              linarith
            apply lt_of_mul_self_lt_mul_self
            linarith
            exact hge3
          linarith
        have hgez2 : (2 - √3) ≠ 0 := by linarith
        have heq1 :  (2 - √3) / (2 - √3) = 1 := by
          apply div_self hgez2
        rw [heq1]
        ring_nf
      have e : (1 + √2) / (2 + √3) * ((2 - √3) / (2 - √3)) = (1 + √2) * (2 - √3) / ((2 + √3) *  (2 - √3))  := by 
        apply div_mul_div_comm  
      rw [e] at heq2
      have heq3 : (2 + √3) * (2 - √3) = 2 * 2 - √3 * √3 := by ring_nf
      rw [heq3] at heq2
      have heq4 : √3 * √3 = 3  := by 
        apply Real.mul_self_sqrt
        linarith
      rw [heq4] at heq2
      rw [show (1 + √2) * (2 - √3) / (2 * 2 - 3) = (1 + √2) * (2 - √3) by ring_nf] at heq2
      have heq5 : (1 + √2) * (2 - √3) = 2 - √3 + 2 * √2 - √6 := by
        ring_nf
        have heq6 : √(2 * 3) =√2 * √3 := by
          apply Real.sqrt_mul
          linarith
        rw [← heq6]
        ring_nf
      rw [heq5] at heq2
      exact heq2
    apply h at heq
    rcases heq with ⟨hA,⟨hB,⟨hC,hD⟩⟩⟩
    rw [hA];rw [hB];rw [hC];rw [hD];
    ring_nf
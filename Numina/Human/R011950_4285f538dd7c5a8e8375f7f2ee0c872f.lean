import Mathlib

open Real
open scoped BigOperators

/- Prove the following inequality for any integer $ N\geq 4$.

\[ \sum_{p\equal{}4}^N \frac{p^2\plus{}2}{(p\minus{}2)^4}<5\] -/

theorem inequalities_78624 (N : ℕ) (hN : 4 ≤ N) :
∑ p in Finset.Icc 4 N, ((p:ℚ)^2 + 2) / (p - 2)^4 < 5 := by

  --We show that for every p ∈ [4,N], we have ((p:ℚ)^2 + 2) / (p - 2)^4 ≤ 4.5 / ((p-3)*(p-2)).
  have cla : ∀ p ∈ Finset.Icc 4 N, ((p:ℚ)^2 + 2) / (p - 2)^4 ≤ 4.5 / ((p-3)*(p-2)) := by 
    intro p hp
    simp at hp
    obtain ⟨pl, pu⟩ := hp

    have pos0 : 0 < (p:ℚ) - 2 := by qify at pl; linarith only [pl]
    have pos1 : 0 < (p:ℚ) - 3 := by qify at pl; linarith only [pl]
    have pos2 : 0 < (((p:ℚ) - 3) * (↑p - 2)) := by exact Left.mul_pos pos1 pos0
    have pos3 : 0 < @HPow.hPow ℚ ℕ ℚ instHPow (↑p - 2) 2 := by exact sq_pos_of_pos pos0
    have pos4 : 0 < @HPow.hPow ℚ ℕ ℚ instHPow (↑p - 2) 4 := by exact pow_pos pos0 4
    have pos5 : 0 < ((p:ℚ) ^ 2 + 2) := by positivity
    have pos6 : 0 < ((p:ℚ) - 3) * (↑p - 2) * (↑p - 2) ^ 2 := by exact Left.mul_pos pos2 pos3

    have t1 : ((p:ℚ)^2 + 2) / (p - 2)^4 ≤ 1/ ((p-3)*(p-2)) * ((p^2+2)/((p-2)^2)) := by 
      field_simp
      have : ((p:ℚ) - 3) * (↑p - 2) * (↑p - 2) ^ 2 ≤ (↑p - 2) ^ 4 := by 
        rw [pow_succ]
        rw [pow_succ]
        simp
        rw [pow_succ];rw [pow_succ];rw [pow_succ];rw [pow_succ]
        simp
        nth_rw 1 [←mul_assoc]
        gcongr
        norm_num
        
      apply div_le_div₀
      linarith
      linarith
      exact pos6
      exact this
      
    have t2 : ((p:ℚ)^2+2)/((p-2)^2) ≤ 4.5 := by 
      refine (div_le_iff₀' pos3).mpr ?_
      rw [pow_two]; rw [pow_two]
      ring_nf
      have : 18 - (p:ℚ) * 18 + ↑p ^ 2 * (9 / 2) - (2 + ↑p ^ 2) = (p-4) * (7*p-8) / 2 := by ring
      have : 0 ≤ ((p:ℚ)-4) * (7*p-8) / 2  := by 
        have t1 : 0 ≤ ((p:ℚ) - 4) := by norm_cast; linarith
        have t2 : 0 ≤ (7*(p:ℚ)-8) := by qify at pl; linarith
        have t3 : 0 ≤ ((p:ℚ)-4) * (7*p-8) := by exact Rat.mul_nonneg t1 t2
        exact Rat.div_nonneg t3 rfl
      linarith
    have t3 : 0 ≤ (((p:ℚ) ^ 2 + 2) / (↑p - 2) ^ 2) := by
      positivity
    have t4 : 0 ≤ 1 / (((p:ℚ) - 3) * (↑p - 2)) := by 
      positivity
    have t5 : 1 / (((p:ℚ) - 3) * (↑p - 2)) * ((↑p ^ 2 + 2) / (↑p - 2) ^ 2) ≤ 1 / (((p:ℚ) - 3) * (↑p - 2)) * 4.5 := by nlinarith
    have : 1 / (((p:ℚ) - 3) * (↑p - 2)) * 4.5 = 4.5 / ((↑p - 3) * (↑p - 2)) := by ring
    rw [this] at t5
    linarith
    
  --Then, the sum of ( (4.5) / ((p-3)*(p-2))) ≤ 4.5 - 4.5/(N-2) < 5.
  have : ∑ p in Finset.Icc 4 N, (((p:ℚ) ^ 2 + 2) / ((p:ℚ) - 2) ^ 4) ≤ ∑ p in Finset.Icc 4 N, ( (4.5:ℚ) / ((p-3)*(p-2))) := by 
    apply Finset.sum_le_sum
    exact cla
  have u : ∑ p in Finset.Icc 4 N, ((4.5:ℚ) / ((p-3)*(p-2))) ≤ 4.5 := by 
    have ind : ∀M:ℕ, ∑ p in Finset.Icc 4 (M+4), ((4.5:ℚ) / ((p-3)*(p-2))) ≤ 4.5 - 4.5/(M+2) := by 
      intro M
      induction' M with M hM

      simp
      norm_num

      have : ∑ p ∈ Finset.Icc 4 (M + 1 + 4), 4.5 / (((p:ℚ) - 3) * (↑p - 2)) = ∑ p ∈ Finset.Icc 4 (M + 4), 4.5 / (((p:ℚ) - 3) * (↑p - 2)) + 4.5 / ((((M + 1 + 4):ℚ) - 3) * ((M + 1 + 4:ℚ) - 2)) := by
        have : Finset.Icc 4 (M + 1 + 4) = Finset.Icc 4 (M + 4) ∪ {(M+1+4)} := by 
          ext x
          simp
          omega

        rw [this]
        rw [Finset.sum_union]
        simp
        simp
      rw [this]
      have : (4.5:ℚ) - 4.5 / (↑M + 2) + (4.5 / ((↑M + 1 + 4 - 3) * (↑M + 1 + 4 - 2))) = 4.5 - 4.5 / (↑(M + 1) + 2) := by 
        have : ((4.5:ℚ) / ((↑M + 1 + 4 - 3) * (↑M + 1 + 4 - 2))) = 4.5/ ((↑M + 2)) - 4.5 / (↑(M + 1)+2) := by 
          have : 0 < (((M:ℚ) + 1 + 4 - 3) * (↑M + 1 + 4 - 2)) := by 
            have t1 : 0 < ((M:ℚ) + 1 + 4 - 3) := by field_simp; linarith
            have t2 : 0 < ((M:ℚ) + 1 + 4 - 2) := by field_simp; linarith
            exact Left.mul_pos t1 t2
          have : 0 < (((M:ℚ) + 2)) := by positivity
          have : 0 < (((M + 1):ℚ)+2) := by positivity
          field_simp
          ring
        rw [this]
        simp
        
      linarith

    have exi : ∃M:ℕ, M+4 = N := by use N-4; omega
    obtain ⟨M,hM⟩ := exi
    specialize ind M
    rw [hM] at ind

    have : 0 ≤ 4.5 / ((M:ℚ) + 2) := by refine Rat.div_nonneg (by norm_num) ?_; positivity
    linarith
    
  linarith

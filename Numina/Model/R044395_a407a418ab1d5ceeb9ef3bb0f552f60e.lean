import Mathlib

set_option maxRecDepth 1000000000

lemma prime_mul_only_dvd (a b c d :ℕ) (ha : a > 0) (h1: Nat.Prime a)
    (h2 : Nat.Prime b) (h3 : c * d = a * b) :
    c=a ∨ c=b ∨ c=1 ∨ c=a*b  := by
  have h4: a ∣ c*d := by use b
  have h1:= Nat.Prime.prime h1
  have h2:= Nat.Prime.prime h2
  have h2:= Prime.dvd_or_dvd h1 h4
  cases h2 with
  | inl hl=>rcases hl with ⟨q,hq⟩
            rw [hq] at h3
            rw [mul_assoc] at h3
            simp at h3
            cases h3 with
            | inl hll=> rw [← hll] at h2
                        have ht:=prime_mul_iff.mp h2
                        cases ht
                        simp_all
                        simp_all
            | inr hlr=> apply False.elim
                        linarith
  | inr hl =>
            rcases hl with ⟨q,hq⟩
            rw [hq] at h3
            rw [mul_comm,mul_assoc] at h3
            simp at h3
            cases h3 with
            | inl hll=> rw [← hll] at h2
                        have ht:=prime_mul_iff.mp h2
                        cases ht
                        simp_all
                        simp_all
            | inr hlr=> apply False.elim
                        linarith

theorem number_theory_4594 (dprice : ℕ ) (camerassold : ℕ) (hint : dprice < 99)
    (hvals : dprice * camerassold = 8137) :
    camerassold = 8137 ∨ camerassold = 103  := by
  have h1 : dprice ∣ 8137 := by
    use camerassold
    all_goals linarith
  have h2 : dprice = 1 ∨ dprice = 79 := by
    interval_cases dprice <;> norm_num at h1 hvals ⊢
    <;> omega 
  rcases h2 with (h | h)
  · -- dprice = 1
    have h3 : camerassold = 8137 := by 
      rw [show dprice = 1 by omega] at hvals 
      omega 
    left 
    linarith 
  · -- dprice = 79 
    have h3 : camerassold = 103 := by 
      rw [show dprice = 79 by omega] at hvals 
      omega 
    right 
    linarith
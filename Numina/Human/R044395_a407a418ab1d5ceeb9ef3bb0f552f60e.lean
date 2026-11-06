import Mathlib

set_option maxRecDepth 1000000000

/- if a,b are prime and ab=cd, then c=a or c=b or c=1 or c=ab -/
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

/- A discount store sells a camera at a price lower than its usual retail price of $99. If the store sells a total of $8137 worth of these cameras and the discounted price per camera is an integer, how many cameras did they sell?-/
theorem number_theory_4594 (dprice : ℕ ) (camerassold : ℕ) (hint : dprice < 99)
    (hvals : dprice * camerassold = 8137) :
    camerassold = 8137 ∨ camerassold = 103  := by
  -- consider 4 cases
  have h1:Nat.Prime 79:= by decide
  have h2:Nat.Prime 103 := by decide
  -- Notice that 8137=79*103 and 79,103 are prime.
  -- It must be `camerassold=79` or `camerassold=103` or `camerassold=1` or `camerassold=8137`
  have h3:=prime_mul_only_dvd 79 103  camerassold dprice (by norm_num) h1 h2 (by simp;linarith)
  cases h3 with
  -- camerassold=79
  | inl hl=>rw[hl] at hvals
            apply False.elim
            linarith -- contradiction
  | inr hr=>cases hr
            -- camerassold=103 is impossible
            aesop
            rename_i ht
            cases ht with
            -- camerassold=1 is impossible
            | inl hl=> rw[hl] at hvals;simp at hvals;rw [hvals] at hint;trivial
            -- camerassold=8137 is desired
            | inr hr=> aesop
